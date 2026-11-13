import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product3
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product4
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product5
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
open CycleSubmission.SharedStackArgs

set_option warningAsError true
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Prepared.ProductGroup8130
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast


open CycleSubmission.Prepared.Arithmetic CycleSubmission.Execution
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def oldModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := v0 * carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := v3 * w11
  let v5 : W := v4 + v2
  let v6 : W := UInt256.mulMod w10 w4 w9
  let v7 : W := v6 + w1
  let v8 : W := UInt256.mulMod w8 w14 w9
  let v9 : W := v8 + v7
  let v10 : W := MachineState.readWord s.memory 192
  let v11 : W := UInt256.mulMod v10 w2 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 0
  let v14 : W := UInt256.mulMod v13 w11 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := v5 * v16
  let v18 : W := UInt256.land w12 v17
  let v19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 224
  let v20 : W := UInt256.mulMod v18 w13 w9
  let v21 : W := v20 + v15
  let v22 : W := UInt256.mulMod (N 2048) v21 w9
  let v23 : W := MachineState.readWord v19 768
  let v24 : W := MachineState.readWord v19 1952
  let v25 : W := v24 * v23
  let v26 : W := v25 + v22
  let v27 : W := UInt256.mulMod v24 v23 w9
  let v28 : W := v27 + v22
  let v29 : W := MachineState.readWord v19 1920
  let v30 : W := v29 * w5
  let v31 : W := v30 + v26
  let v32 : W := UInt256.mulMod v29 w5 w9
  let v33 : W := v32 + v28
  let v34 : W := MachineState.readWord v19 1888
  let v35 : W := v34 * w6
  let v36 : W := v35 + v31
  let v37 : W := UInt256.mulMod v34 w6 w9
  let v38 : W := v37 + v33
  let v39 : W := MachineState.readWord v19 32
  let v40 : W := MachineState.readWord v19 1856
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord v19 64
  let v46 : W := MachineState.readWord v19 1824
  let v47 : W := v46 * v45
  let v48 : W := v47 + v42
  let v49 : W := UInt256.mulMod v46 v45 w9
  let v50 : W := v49 + v44
  let v51 : W := MachineState.readWord v19 96
  let v52 : W := MachineState.readWord v19 1792
  let v53 : W := v52 * v51
  let v54 : W := v53 + v48
  let v55 : W := UInt256.mulMod v52 v51 w9
  let v56 : W := v55 + v50
  let v57 : W := w10 * w7
  let v58 : W := v57 + v54
  let v59 : W := w8 * w4
  let v60 : W := v59 + v58
  let v61 : W := MachineState.readWord v19 192
  let v62 : W := v61 * w14
  let v63 : W := v62 + v60
  let v64 : W := MachineState.readWord v19 0
  let v65 : W := v64 * w2
  let v66 : W := v65 + v63
  let v67 : W := MachineState.readWord v19 224
  let v68 : W := v67 * w11
  let v69 : W := v68 + v66
  let v70 : W := UInt256.mulMod w10 w7 w9
  let v71 : W := v70 + v56
  let v72 : W := UInt256.mulMod w8 w4 w9
  let v73 : W := v72 + v71
  let v74 : W := MachineState.readWord v19 192
  let v75 : W := UInt256.mulMod v74 w14 w9
  let v76 : W := v75 + v73
  let v77 : W := MachineState.readWord v19 0
  let v78 : W := UInt256.mulMod v77 w2 w9
  let v79 : W := v78 + v76
  let v80 : W := MachineState.readWord v19 224
  let v81 : W := UInt256.mulMod v80 w11 w9
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord v19 2720
  let v84 : W := v69 * v83
  let v85 : W := UInt256.land w12 v84
  let v86 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v85.toNat 32) 1216
  let v87 : W := UInt256.mulMod v85 w13 w9
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod (N 2048) v88 w9
  let v90 : W := MachineState.readWord v86 768
  let v91 : W := MachineState.readWord v86 1984
  let v92 : W := v91 * v90
  let v93 : W := v92 + v89
  let v94 : W := UInt256.mulMod v91 v90 w9
  let v95 : W := v94 + v89
  let v96 : W := MachineState.readWord v86 1952
  let v97 : W := v96 * w5
  let v98 : W := v97 + v93
  let v99 : W := UInt256.mulMod v96 w5 w9
  let v100 : W := v99 + v95
  let v101 : W := MachineState.readWord v86 1920
  let v102 : W := v101 * w6
  let v103 : W := v102 + v98
  let v104 : W := UInt256.mulMod v101 w6 w9
  let v105 : W := v104 + v100
  let v106 : W := MachineState.readWord v86 32
  let v107 : W := MachineState.readWord v86 1888
  let v108 : W := v107 * v106
  let v109 : W := v108 + v103
  let v110 : W := UInt256.mulMod v107 v106 w9
  let v111 : W := v110 + v105
  let v112 : W := MachineState.readWord v86 64
  let v113 : W := MachineState.readWord v86 1856
  let v114 : W := v113 * v112
  let v115 : W := v114 + v109
  let v116 : W := UInt256.mulMod v113 v112 w9
  let v117 : W := v116 + v111
  let v118 : W := MachineState.readWord v86 96
  let v119 : W := MachineState.readWord v86 1824
  let v120 : W := v119 * v118
  let v121 : W := v120 + v115
  let v122 : W := UInt256.mulMod v119 v118 w9
  let v123 : W := v122 + v117
  let v124 : W := MachineState.readWord v86 128
  let v125 : W := MachineState.readWord v86 1792
  let v126 : W := v125 * v124
  let v127 : W := v126 + v121
  let v128 : W := UInt256.mulMod v125 v124 w9
  let v129 : W := v128 + v123
  let v130 : W := w10 * w3
  let v131 : W := v130 + v127
  let v132 : W := w8 * w7
  let v133 : W := v132 + v131
  let v134 : W := MachineState.readWord v86 192
  let v135 : W := v134 * w4
  let v136 : W := v135 + v133
  let v137 : W := MachineState.readWord v86 0
  let v138 : W := v137 * w14
  let v139 : W := v138 + v136
  let v140 : W := MachineState.readWord v86 224
  let v141 : W := v140 * w2
  let v142 : W := v141 + v139
  let v143 : W := MachineState.readWord v86 1216
  let v144 : W := v143 * w11
  let v145 : W := v144 + v142
  let v146 : W := UInt256.mulMod w10 w3 w9
  let v147 : W := v146 + v129
  let v148 : W := UInt256.mulMod w8 w7 w9
  let v149 : W := v148 + v147
  {s with pc := N 8529, memory := v86, stack := w4 :: w9 :: v149 :: v145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

def newpart0Program : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL]

def newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := v3 * x12
  {s with pc := N 8158, memory := s.memory, stack := v4 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := N 8149, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart0Program, newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha192, hf192]


def newpart1Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x11 x5 x10
  let v2 : W := v1 + x2
  {s with pc := N 8166, memory := s.memory, stack := x10 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart1Program {s with pc := N 8158, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart1Program, newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart2Program : List Instr :=
  [
  .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x15 x0
  let v1 : W := v0 + x1
  let v2 : W := MachineState.readWord s.memory 192
  {s with pc := N 8175, memory := s.memory, stack := v2 :: x3 :: x10 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := N 8166, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart2Program, newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def newpart3Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod v2 x14 x12
  let v4 : W := v3 + v1
  {s with pc := N 8183, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart3Program {s with pc := N 8175, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart3Program, newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]


def newpart4Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩)]

def newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x1 * v0
  {s with pc := N 8193, memory := s.memory, stack := x12 :: v1 :: x13 :: x9 :: x0 :: x9 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart4Program {s with pc := N 8183, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart4Program, newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def newpart5Program : List Instr :=
  [
  .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 224,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD]

def newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x0 x1
  let v1 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v0.toNat 32) 224
  let v2 : W := UInt256.mulMod v0 x2 x3
  let v3 : W := v2 + x4
  let v4 : W := UInt256.mulMod (N 2048) v3 x5
  {s with pc := N 8204, memory := v1, stack := v4 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart5Program {s with pc := N 8193, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart5Program, newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart6Program : List Instr :=
  [
  .push 2 1920,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨1, by decide⟩)]

def newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := MachineState.readWord s.memory 768
  let v2 : W := MachineState.readWord s.memory 1952
  {s with pc := N 8218, memory := s.memory, stack := v2 :: x8 :: v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest}

theorem newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart6Program {s with pc := N 8204, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: rest} =
      some (newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart6Program, newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1920, hf1920, ha1952, hf1952]


def newpart7Program : List Instr :=
  [
  .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩)]

def newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x3 x0 x1
  let v1 : W := x3 * x2
  let v2 : W := x5 + v1
  {s with pc := N 8226, memory := s.memory, stack := x4 :: x13 :: v2 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart7Program {s with pc := N 8218, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart7Program, newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart8Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD]

def newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x0 x1
  let v1 : W := x9 * x4
  let v2 : W := v1 + x2
  let v3 : W := x5 + x3
  {s with pc := N 8234, memory := s.memory, stack := v3 :: v0 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart8Program {s with pc := N 8226, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart8Program, newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart9Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 1888
  {s with pc := N 8244, memory := s.memory, stack := v1 :: x7 :: x2 :: x7 :: x10 :: v0 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart9Program {s with pc := N 8234, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart9Program, newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1888, hf1888]


def newpart10Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD]

def newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 32
  {s with pc := N 8253, memory := s.memory, stack := v4 :: x14 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart10Program {s with pc := N 8244, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart10Program, newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def newpart11Program : List Instr :=
  [
  .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩)]

def newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1856
  let v1 : W := v0 * x0
  let v2 : W := v1 + x3
  {s with pc := N 8263, memory := s.memory, stack := v0 :: x0 :: x1 :: x2 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart11Program {s with pc := N 8253, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart11Program, newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1856, hf1856]


def newpart12Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD]

def newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 64
  let v4 : W := MachineState.readWord s.memory 1824
  {s with pc := N 8275, memory := s.memory, stack := v4 :: v3 :: v2 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart12Program {s with pc := N 8263, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart12Program, newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha96, hf96, ha1824, hf1824]


def newpart13Program : List Instr :=
  [
  .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD]

def newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x12
  let v1 : W := x1 * x0
  let v2 : W := MachineState.readWord s.memory 1792
  {s with pc := N 8285, memory := s.memory, stack := v2 :: v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart13Program {s with pc := N 8275, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart13Program, newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def newpart14Program : List Instr :=
  [
  .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD]

def newpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x5 + x1
  let v1 : W := x4 + x2
  let v2 : W := UInt256.mulMod x0 x3 x13
  {s with pc := N 8293, memory := s.memory, stack := v2 :: v1 :: x3 :: v0 :: x0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart14Program {s with pc := N 8285, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart14Program, newpart14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart15Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD]

def newpart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x2
  let v2 : W := v1 + x3
  let v3 : W := x13 * x10
  let v4 : W := v3 + v2
  {s with pc := N 8301, memory := s.memory, stack := v4 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart15Program {s with pc := N 8293, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart15Program, newpart15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart16Program : List Instr :=
  [
  .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL]

def newpart16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x8 * x4
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 192
  let v3 : W := v2 * x14
  {s with pc := N 8310, memory := s.memory, stack := v3 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart16Program {s with pc := N 8301, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart16Program, newpart16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def newpart17Program : List Instr :=
  [
  .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 224,
   .op .MLOAD]

def newpart17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 0
  let v2 : W := v1 * x3
  let v3 : W := v2 + v0
  let v4 : W := MachineState.readWord s.memory 224
  {s with pc := N 8320, memory := s.memory, stack := v4 :: x12 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart17Program {s with pc := N 8310, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart17Program, newpart17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def newpart18Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart18Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x12 x9 x11
  let v3 : W := v2 + x3
  {s with pc := N 8328, memory := s.memory, stack := v3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart18_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart18Program {s with pc := N 8320, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart18Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart18Program, newpart18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart19Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def newpart19Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x4 x9
  let v1 : W := v0 + x0
  let v2 : W := MachineState.readWord s.memory 192
  {s with pc := N 8338, memory := s.memory, stack := v2 :: x14 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart19_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart19Program {s with pc := N 8328, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart19Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart19Program, newpart19Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def newpart20Program : List Instr :=
  [
  .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD]

def newpart20Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := UInt256.mulMod v2 x5 x12
  let v4 : W := v3 + v1
  {s with pc := N 8346, memory := s.memory, stack := v4 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart20_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart20Program {s with pc := N 8338, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart20Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart20Program, newpart20Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]


def newpart21Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩)]

def newpart21Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := UInt256.mulMod v0 x11 x9
  let v2 : W := v1 + x0
  {s with pc := N 8355, memory := s.memory, stack := x13 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart21_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart21Program {s with pc := N 8346, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart21Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart21Program, newpart21Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart22Program : List Instr :=
  [
  .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩)]

def newpart22Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 2720
  let v1 : W := x3 * v0
  let v2 : W := UInt256.land x14 v1
  {s with pc := N 8365, memory := s.memory, stack := v2 :: v2 :: x0 :: x1 :: x2 :: x1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart22_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart22Program {s with pc := N 8355, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart22Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha2720 : (2720 : W).toNat = 2720 := rfl
  have hf2720 := Monpro.activeWords_fix s 2720 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart22Program, newpart22Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2720, hf2720]


def newpart23Program : List Instr :=
  [
  .push 2 1216,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1952,
   .op .MLOAD]

def newpart23Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 1216
  let v1 : W := UInt256.mulMod x1 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := UInt256.mulMod (N 2048) v2 x5
  let v4 : W := MachineState.readWord v0 1952
  {s with pc := N 8379, memory := v0, stack := v4 :: v3 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart23_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart23Program {s with pc := N 8365, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart23Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart23Program, newpart23Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1216, hf1216, ha1952, hf1952]


def newpart24Program : List Instr :=
  [
  .push 2 768,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD]

def newpart24Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 768
  let v1 : W := MachineState.readWord s.memory 1984
  let v2 : W := UInt256.mulMod v0 v1 x9
  {s with pc := N 8391, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart24_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart24Program {s with pc := N 8379, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart24Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha768 : (768 : W).toNat = 768 := rfl
  have hf768 := Monpro.activeWords_fix s 768 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart24Program, newpart24Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha768, hf768, ha1984, hf1984]


def newpart25Program : List Instr :=
  [
  .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD]

def newpart25Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x2 * x1
  let v1 : W := x4 + v0
  let v2 : W := UInt256.mulMod x8 x3 x12
  {s with pc := N 8399, memory := s.memory, stack := v2 :: v1 :: x0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart25_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart25Program {s with pc := N 8391, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart25Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart25Program, newpart25Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart26Program : List Instr :=
  [
  .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def newpart26Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x8 * x3
  let v1 : W := v0 + x1
  let v2 : W := x4 + x2
  let v3 : W := v2 + x0
  {s with pc := N 8407, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart26_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart26Program {s with pc := N 8399, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart26Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart26Program, newpart26Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart27Program : List Instr :=
  [
  .op (.Dup ⟨7, by decide⟩),
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD]

def newpart27Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1920
  let v1 : W := v0 * x7
  let v2 : W := v1 + x2
  {s with pc := N 8417, memory := s.memory, stack := v2 :: x7 :: x0 :: x1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart27_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart27Program {s with pc := N 8407, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart27Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart27Program, newpart27Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1920, hf1920]


def newpart28Program : List Instr :=
  [
  .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD]

def newpart28Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 32
  let v3 : W := MachineState.readWord s.memory 1888
  {s with pc := N 8428, memory := s.memory, stack := v3 :: v2 :: x12 :: v1 :: x0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart28_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart28Program {s with pc := N 8417, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart28Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  have ha1888 : (1888 : W).toNat = 1888 := rfl
  have hf1888 := Monpro.activeWords_fix s 1888 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart28Program, newpart28Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32, ha1888, hf1888]


def newpart29Program : List Instr :=
  [
  .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD]

def newpart29Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x4
  let v2 : W := UInt256.mulMod x0 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 8436, memory := s.memory, stack := v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart29_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart29Program {s with pc := N 8428, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart29Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart29Program, newpart29Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart30Program : List Instr :=
  [
  .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart30Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 64
  let v1 : W := MachineState.readWord s.memory 1856
  {s with pc := N 8447, memory := s.memory, stack := v1 :: v0 :: x1 :: v0 :: x9 :: x0 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart30_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart30Program {s with pc := N 8436, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart30Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha1856 : (1856 : W).toNat = 1856 := rfl
  have hf1856 := Monpro.activeWords_fix s 1856 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart30Program, newpart30Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha1856, hf1856]


def newpart31Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD]

def newpart31Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x6 x3 x4
  let v3 : W := v2 + x5
  let v4 : W := MachineState.readWord s.memory 128
  let v5 : W := MachineState.readWord s.memory 96
  {s with pc := N 8458, memory := s.memory, stack := v5 :: v4 :: v3 :: v1 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest}

theorem newpart31_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart31Program {s with pc := N 8447, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: x20 :: rest} =
      some (newpart31Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart31Program, newpart31Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha128, hf128]


def newpart32Program : List Instr :=
  [
  .push 2 1824,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL]

def newpart32Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1824
  let v1 : W := UInt256.mulMod x0 v0 x11
  let v2 : W := x0 * v0
  {s with pc := N 8468, memory := s.memory, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart32_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart32Program {s with pc := N 8458, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart32Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 22) : rest.length + j < 1024 := by omega
  have ha1824 : (1824 : W).toNat = 1824 := rfl
  have hf1824 := Monpro.activeWords_fix s 1824 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart32Program, newpart32Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1824, hf1824]


def newpart33Program : List Instr :=
  [
  .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩)]

def newpart33Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1792
  let v1 : W := x4 + x0
  let v2 : W := x3 + x1
  {s with pc := N 8478, memory := s.memory, stack := x2 :: x12 :: v2 :: x2 :: v1 :: v0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart33_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart33Program {s with pc := N 8468, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart33Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha1792 : (1792 : W).toNat = 1792 := rfl
  have hf1792 := Monpro.activeWords_fix s 1792 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart33Program, newpart33Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1792, hf1792]


def newpart34Program : List Instr :=
  [
  .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨11, by decide⟩)]

def newpart34Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := x5 * x3
  let v3 : W := v2 + x4
  {s with pc := N 8486, memory := s.memory, stack := x14 :: x7 :: v3 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart34_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart34Program {s with pc := N 8478, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart34Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart34Program, newpart34Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart35Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD]

def newpart35Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x10 * x9
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 192
  {s with pc := N 8496, memory := s.memory, stack := v4 :: x6 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart35_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart35Program {s with pc := N 8486, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart35Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha192 : (192 : W).toNat = 192 := rfl
  have hf192 := Monpro.activeWords_fix s 192 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart35Program, newpart35Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha192, hf192]


def newpart36Program : List Instr :=
  [
  .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩)]

def newpart36Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 0
  let v3 : W := v2 * x16
  let v4 : W := v3 + v1
  {s with pc := N 8504, memory := s.memory, stack := x4 :: v4 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart36_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart36Program {s with pc := N 8496, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart36Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart36Program, newpart36Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0]


def newpart37Program : List Instr :=
  [
  .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL]

def newpart37Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 224
  let v1 : W := v0 * x0
  let v2 : W := v1 + x1
  let v3 : W := MachineState.readWord s.memory 1216
  let v4 : W := v3 * x12
  {s with pc := N 8515, memory := s.memory, stack := v4 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart37_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart37Program {s with pc := N 8504, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart37Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  have ha1216 : (1216 : W).toNat = 1216 := rfl
  have hf1216 := Monpro.activeWords_fix s 1216 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart37Program, newpart37Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224, ha1216, hf1216]


def newpart38Program : List Instr :=
  [
  .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩)]

def newpart38Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x11 x4 x10
  let v2 : W := v1 + x2
  {s with pc := N 8523, memory := s.memory, stack := x10 :: v2 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart38_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart38Program {s with pc := N 8515, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart38Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart38Program, newpart38Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart39Program : List Instr :=
  [
  .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newpart39Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x9 x8 x0
  let v1 : W := v0 + x1
  {s with pc := N 8529, memory := s.memory, stack := x5 :: x10 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart39_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart39Program {s with pc := N 8523, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart39Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart39Program, newpart39Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newProgram : List Instr :=
  [
  .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 224,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1920,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 1 96,
   .op .MLOAD,
   .push 1 64,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨15, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .push 2 2720,
   .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨15, by decide⟩),
   .op .AND,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 1216,
   .op .MSTORE,
   .op .MULMOD,
   .op .ADD,
   .push 2 2048,
   .op .MULMOD,
   .push 2 1952,
   .op .MLOAD,
   .push 2 768,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 32,
   .op .MLOAD,
   .push 2 1888,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .push 1 64,
   .op .MLOAD,
   .push 2 1856,
   .op .MLOAD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .push 1 128,
   .op .MLOAD,
   .push 1 96,
   .op .MLOAD,
   .push 2 1824,
   .op .MLOAD,
   .op (.Dup ⟨12, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩),
   .op .MUL,
   .push 2 1792,
   .op .MLOAD,
   .op (.Swap ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨4, by decide⟩),
   .push 1 192,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨14, by decide⟩),
   .push 0 0,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .push 1 224,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Dup ⟨11, by decide⟩),
   .push 2 1216,
   .op .MLOAD,
   .op .MUL,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨12, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨10, by decide⟩),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup ⟨9, by decide⟩),
   .op (.Dup ⟨5, by decide⟩)]

def newModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := v0 * carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := v3 * w11
  let v5 : W := v4 + v2
  let v6 : W := UInt256.mulMod w10 w4 w9
  let v7 : W := v6 + w1
  let v8 : W := UInt256.mulMod w8 w14 w9
  let v9 : W := v8 + v7
  let v10 : W := MachineState.readWord s.memory 192
  let v11 : W := UInt256.mulMod v10 w2 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 0
  let v14 : W := UInt256.mulMod v13 w11 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := v5 * v16
  let v18 : W := UInt256.land w12 v17
  let v19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 224
  let v20 : W := UInt256.mulMod v18 w13 w9
  let v21 : W := v20 + v15
  let v22 : W := UInt256.mulMod (N 2048) v21 w9
  let v23 : W := MachineState.readWord v19 1920
  let v24 : W := MachineState.readWord v19 768
  let v25 : W := MachineState.readWord v19 1952
  let v26 : W := UInt256.mulMod v24 v25 w9
  let v27 : W := v24 * v25
  let v28 : W := v22 + v27
  let v29 : W := UInt256.mulMod w5 v23 w9
  let v30 : W := w5 * v23
  let v31 : W := v30 + v28
  let v32 : W := v22 + v26
  let v33 : W := v32 + v29
  let v34 : W := MachineState.readWord v19 1888
  let v35 : W := v34 * w6
  let v36 : W := v35 + v31
  let v37 : W := UInt256.mulMod v34 w6 w9
  let v38 : W := v37 + v33
  let v39 : W := MachineState.readWord v19 32
  let v40 : W := MachineState.readWord v19 1856
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord v19 96
  let v46 : W := MachineState.readWord v19 64
  let v47 : W := MachineState.readWord v19 1824
  let v48 : W := UInt256.mulMod v46 v47 w9
  let v49 : W := v46 * v47
  let v50 : W := MachineState.readWord v19 1792
  let v51 : W := v42 + v49
  let v52 : W := v44 + v48
  let v53 : W := UInt256.mulMod v50 v45 w9
  let v54 : W := v53 + v52
  let v55 : W := v50 * v45
  let v56 : W := v55 + v51
  let v57 : W := w10 * w7
  let v58 : W := v57 + v56
  let v59 : W := w8 * w4
  let v60 : W := v59 + v58
  let v61 : W := MachineState.readWord v19 192
  let v62 : W := v61 * w14
  let v63 : W := v62 + v60
  let v64 : W := MachineState.readWord v19 0
  let v65 : W := v64 * w2
  let v66 : W := v65 + v63
  let v67 : W := MachineState.readWord v19 224
  let v68 : W := v67 * w11
  let v69 : W := v68 + v66
  let v70 : W := UInt256.mulMod w10 w7 w9
  let v71 : W := v70 + v54
  let v72 : W := UInt256.mulMod w8 w4 w9
  let v73 : W := v72 + v71
  let v74 : W := MachineState.readWord v19 192
  let v75 : W := UInt256.mulMod v74 w14 w9
  let v76 : W := v75 + v73
  let v77 : W := MachineState.readWord v19 0
  let v78 : W := UInt256.mulMod v77 w2 w9
  let v79 : W := v78 + v76
  let v80 : W := MachineState.readWord v19 224
  let v81 : W := UInt256.mulMod v80 w11 w9
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord v19 2720
  let v84 : W := v69 * v83
  let v85 : W := UInt256.land w12 v84
  let v86 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v85.toNat 32) 1216
  let v87 : W := UInt256.mulMod v85 w13 w9
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod (N 2048) v88 w9
  let v90 : W := MachineState.readWord v86 1952
  let v91 : W := MachineState.readWord v86 768
  let v92 : W := MachineState.readWord v86 1984
  let v93 : W := UInt256.mulMod v91 v92 w9
  let v94 : W := v91 * v92
  let v95 : W := v89 + v94
  let v96 : W := UInt256.mulMod w5 v90 w9
  let v97 : W := w5 * v90
  let v98 : W := v97 + v95
  let v99 : W := v89 + v93
  let v100 : W := v99 + v96
  let v101 : W := MachineState.readWord v86 1920
  let v102 : W := v101 * w6
  let v103 : W := v102 + v98
  let v104 : W := UInt256.mulMod v101 w6 w9
  let v105 : W := v104 + v100
  let v106 : W := MachineState.readWord v86 32
  let v107 : W := MachineState.readWord v86 1888
  let v108 : W := v107 * v106
  let v109 : W := v108 + v103
  let v110 : W := UInt256.mulMod v107 v106 w9
  let v111 : W := v110 + v105
  let v112 : W := MachineState.readWord v86 64
  let v113 : W := MachineState.readWord v86 1856
  let v114 : W := v113 * v112
  let v115 : W := v114 + v109
  let v116 : W := UInt256.mulMod v113 v112 w9
  let v117 : W := v116 + v111
  let v118 : W := MachineState.readWord v86 128
  let v119 : W := MachineState.readWord v86 96
  let v120 : W := MachineState.readWord v86 1824
  let v121 : W := UInt256.mulMod v119 v120 w9
  let v122 : W := v119 * v120
  let v123 : W := MachineState.readWord v86 1792
  let v124 : W := v115 + v122
  let v125 : W := v117 + v121
  let v126 : W := UInt256.mulMod v123 v118 w9
  let v127 : W := v126 + v125
  let v128 : W := v123 * v118
  let v129 : W := v128 + v124
  let v130 : W := w10 * w3
  let v131 : W := v130 + v129
  let v132 : W := w8 * w7
  let v133 : W := v132 + v131
  let v134 : W := MachineState.readWord v86 192
  let v135 : W := v134 * w4
  let v136 : W := v135 + v133
  let v137 : W := MachineState.readWord v86 0
  let v138 : W := v137 * w14
  let v139 : W := v138 + v136
  let v140 : W := MachineState.readWord v86 224
  let v141 : W := v140 * w2
  let v142 : W := v141 + v139
  let v143 : W := MachineState.readWord v86 1216
  let v144 : W := v143 * w11
  let v145 : W := v144 + v142
  let v146 : W := UInt256.mulMod w10 w3 w9
  let v147 : W := v146 + v127
  let v148 : W := UInt256.mulMod w8 w7 w9
  let v149 : W := v148 + v147
  {s with pc := N 8529, memory := v86, stack := w4 :: w9 :: v149 :: v145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem new_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := N 8149, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := MachineState.readWord s.memory 192
  let v1 : W := v0 * carry
  let v2 : W := v1 + w0
  let v3 : W := MachineState.readWord s.memory 0
  let v4 : W := v3 * w11
  let v5 : W := v4 + v2
  let v6 : W := UInt256.mulMod w10 w4 w9
  let v7 : W := v6 + w1
  let v8 : W := UInt256.mulMod w8 w14 w9
  let v9 : W := v8 + v7
  let v10 : W := MachineState.readWord s.memory 192
  let v11 : W := UInt256.mulMod v10 w2 w9
  let v12 : W := v11 + v9
  let v13 : W := MachineState.readWord s.memory 0
  let v14 : W := UInt256.mulMod v13 w11 w9
  let v15 : W := v14 + v12
  let v16 : W := MachineState.readWord s.memory 2720
  let v17 : W := v5 * v16
  let v18 : W := UInt256.land w12 v17
  let v19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 224
  let v20 : W := UInt256.mulMod v18 w13 w9
  let v21 : W := v20 + v15
  let v22 : W := UInt256.mulMod (N 2048) v21 w9
  let v23 : W := MachineState.readWord v19 1920
  let v24 : W := MachineState.readWord v19 768
  let v25 : W := MachineState.readWord v19 1952
  let v26 : W := UInt256.mulMod v24 v25 w9
  let v27 : W := v24 * v25
  let v28 : W := v22 + v27
  let v29 : W := UInt256.mulMod w5 v23 w9
  let v30 : W := w5 * v23
  let v31 : W := v30 + v28
  let v32 : W := v22 + v26
  let v33 : W := v32 + v29
  let v34 : W := MachineState.readWord v19 1888
  let v35 : W := v34 * w6
  let v36 : W := v35 + v31
  let v37 : W := UInt256.mulMod v34 w6 w9
  let v38 : W := v37 + v33
  let v39 : W := MachineState.readWord v19 32
  let v40 : W := MachineState.readWord v19 1856
  let v41 : W := v40 * v39
  let v42 : W := v41 + v36
  let v43 : W := UInt256.mulMod v40 v39 w9
  let v44 : W := v43 + v38
  let v45 : W := MachineState.readWord v19 96
  let v46 : W := MachineState.readWord v19 64
  let v47 : W := MachineState.readWord v19 1824
  let v48 : W := UInt256.mulMod v46 v47 w9
  let v49 : W := v46 * v47
  let v50 : W := MachineState.readWord v19 1792
  let v51 : W := v42 + v49
  let v52 : W := v44 + v48
  let v53 : W := UInt256.mulMod v50 v45 w9
  let v54 : W := v53 + v52
  let v55 : W := v50 * v45
  let v56 : W := v55 + v51
  let v57 : W := w10 * w7
  let v58 : W := v57 + v56
  let v59 : W := w8 * w4
  let v60 : W := v59 + v58
  let v61 : W := MachineState.readWord v19 192
  let v62 : W := v61 * w14
  let v63 : W := v62 + v60
  let v64 : W := MachineState.readWord v19 0
  let v65 : W := v64 * w2
  let v66 : W := v65 + v63
  let v67 : W := MachineState.readWord v19 224
  let v68 : W := v67 * w11
  let v69 : W := v68 + v66
  let v70 : W := UInt256.mulMod w10 w7 w9
  let v71 : W := v70 + v54
  let v72 : W := UInt256.mulMod w8 w4 w9
  let v73 : W := v72 + v71
  let v74 : W := MachineState.readWord v19 192
  let v75 : W := UInt256.mulMod v74 w14 w9
  let v76 : W := v75 + v73
  let v77 : W := MachineState.readWord v19 0
  let v78 : W := UInt256.mulMod v77 w2 w9
  let v79 : W := v78 + v76
  let v80 : W := MachineState.readWord v19 224
  let v81 : W := UInt256.mulMod v80 w11 w9
  let v82 : W := v81 + v79
  let v83 : W := MachineState.readWord v19 2720
  let v84 : W := v69 * v83
  let v85 : W := UInt256.land w12 v84
  let v86 : ByteArray := MachineState.writeBytes v19 (Data.Bytes.natToBytesPadded v85.toNat 32) 1216
  let v87 : W := UInt256.mulMod v85 w13 w9
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod (N 2048) v88 w9
  let v90 : W := MachineState.readWord v86 1952
  let v91 : W := MachineState.readWord v86 768
  let v92 : W := MachineState.readWord v86 1984
  let v93 : W := UInt256.mulMod v91 v92 w9
  let v94 : W := v91 * v92
  let v95 : W := v89 + v94
  let v96 : W := UInt256.mulMod w5 v90 w9
  let v97 : W := w5 * v90
  let v98 : W := v97 + v95
  let v99 : W := v89 + v93
  let v100 : W := v99 + v96
  let v101 : W := MachineState.readWord v86 1920
  let v102 : W := v101 * w6
  let v103 : W := v102 + v98
  let v104 : W := UInt256.mulMod v101 w6 w9
  let v105 : W := v104 + v100
  let v106 : W := MachineState.readWord v86 32
  let v107 : W := MachineState.readWord v86 1888
  let v108 : W := v107 * v106
  let v109 : W := v108 + v103
  let v110 : W := UInt256.mulMod v107 v106 w9
  let v111 : W := v110 + v105
  let v112 : W := MachineState.readWord v86 64
  let v113 : W := MachineState.readWord v86 1856
  let v114 : W := v113 * v112
  let v115 : W := v114 + v109
  let v116 : W := UInt256.mulMod v113 v112 w9
  let v117 : W := v116 + v111
  let v118 : W := MachineState.readWord v86 128
  let v119 : W := MachineState.readWord v86 96
  let v120 : W := MachineState.readWord v86 1824
  let v121 : W := UInt256.mulMod v119 v120 w9
  let v122 : W := v119 * v120
  let v123 : W := MachineState.readWord v86 1792
  let v124 : W := v115 + v122
  let v125 : W := v117 + v121
  let v126 : W := UInt256.mulMod v123 v118 w9
  let v127 : W := v126 + v125
  let v128 : W := v123 * v118
  let v129 : W := v128 + v124
  let v130 : W := w10 * w3
  let v131 : W := v130 + v129
  let v132 : W := w8 * w7
  let v133 : W := v132 + v131
  let v134 : W := MachineState.readWord v86 192
  let v135 : W := v134 * w4
  let v136 : W := v135 + v133
  let v137 : W := MachineState.readWord v86 0
  let v138 : W := v137 * w14
  let v139 : W := v138 + v136
  let v140 : W := MachineState.readWord v86 224
  let v141 : W := v140 * w2
  let v142 : W := v141 + v139
  let v143 : W := MachineState.readWord v86 1216
  let v144 : W := v143 * w11
  let v145 : W := v144 + v142
  let v146 : W := UInt256.mulMod w10 w3 w9
  let v147 : W := v146 + v127
  let v148 : W := UInt256.mulMod w8 w7 w9
  let v149 : W := v148 + v147
  have h0 : runInstructions newpart0Program {s with pc := N 8149, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8158, memory := s.memory, stack := v4 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart0Model, v0, v1, v2, v3, v4] using newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := N 8158, memory := s.memory, stack := v4 :: v2 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8166, memory := s.memory, stack := w9 :: v7 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart1Model, v5, v6, v7] using newpart1_run (s) (v4) (v2) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions newpart2Program {s with pc := N 8166, memory := s.memory, stack := w9 :: v7 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8175, memory := s.memory, stack := v10 :: w2 :: w9 :: v9 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart2Model, v8, v9, v10] using newpart2_run (s) (w9) (v7) (v5) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions newpart3Program {s with pc := N 8175, memory := s.memory, stack := v10 :: w2 :: w9 :: v9 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8183, memory := s.memory, stack := v15 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart3Model, v11, v12, v13, v14, v15] using newpart3_run (s) (v10) (w2) (w9) (v9) (v5) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions newpart4Program {s with pc := N 8183, memory := s.memory, stack := v15 :: v5 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8193, memory := s.memory, stack := w12 :: v17 :: w13 :: w9 :: v15 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart4Model, v16, v17] using newpart4_run (s) (v15) (v5) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions newpart5Program {s with pc := N 8193, memory := s.memory, stack := w12 :: v17 :: w13 :: w9 :: v15 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8204, memory := v19, stack := v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart5Model, v18, v19, v20, v21, v22] using newpart5_run (s) (w12) (v17) (w13) (w9) (v15) (w9) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions newpart6Program {s with pc := N 8204, memory := v19, stack := v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8218, memory := v19, stack := v25 :: w9 :: v25 :: v24 :: v23 :: v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart6Model, v23, v24, v25] using newpart6_run ({s with memory := v19}) (v22) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h7 : runInstructions newpart7Program {s with pc := N 8218, memory := v19, stack := v25 :: w9 :: v25 :: v24 :: v23 :: v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8226, memory := v19, stack := v23 :: w9 :: v28 :: v26 :: v23 :: v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart7Model, v26, v27, v28] using newpart7_run ({s with memory := v19}) (v25) (w9) (v25) (v24) (v23) (v22) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions newpart8Program {s with pc := N 8226, memory := v19, stack := v23 :: w9 :: v28 :: v26 :: v23 :: v22 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8234, memory := v19, stack := v32 :: v29 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart8Model, v29, v30, v31, v32] using newpart8_run ({s with memory := v19}) (v23) (w9) (v28) (v26) (v23) (v22) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions newpart9Program {s with pc := N 8234, memory := v19, stack := v32 :: v29 :: v31 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8244, memory := v19, stack := v34 :: w6 :: v31 :: w6 :: w9 :: v33 :: v34 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart9Model, v33, v34] using newpart9_run ({s with memory := v19}) (v32) (v29) (v31) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions newpart10Program {s with pc := N 8244, memory := v19, stack := v34 :: w6 :: v31 :: w6 :: w9 :: v33 :: v34 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8253, memory := v19, stack := v39 :: w9 :: v38 :: v36 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart10Model, v35, v36, v37, v38, v39] using newpart10_run ({s with memory := v19}) (v34) (w6) (v31) (w6) (w9) (v33) (v34) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h11 : runInstructions newpart11Program {s with pc := N 8253, memory := v19, stack := v39 :: w9 :: v38 :: v36 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8263, memory := v19, stack := v40 :: v39 :: w9 :: v38 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart11Model, v40, v41, v42] using newpart11_run ({s with memory := v19}) (v39) (w9) (v38) (v36) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h12 : runInstructions newpart12Program {s with pc := N 8263, memory := v19, stack := v40 :: v39 :: w9 :: v38 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8275, memory := v19, stack := v47 :: v46 :: v45 :: v44 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart12Model, v43, v44, v45, v46, v47] using newpart12_run ({s with memory := v19}) (v40) (v39) (w9) (v38) (v42) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h13 : runInstructions newpart13Program {s with pc := N 8275, memory := v19, stack := v47 :: v46 :: v45 :: v44 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8285, memory := v19, stack := v50 :: v49 :: v48 :: v45 :: v44 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart13Model, v48, v49, v50] using newpart13_run ({s with memory := v19}) (v47) (v46) (v45) (v44) (v42) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h14 : runInstructions newpart14Program {s with pc := N 8285, memory := v19, stack := v50 :: v49 :: v48 :: v45 :: v44 :: v42 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8293, memory := v19, stack := v53 :: v52 :: v45 :: v51 :: v50 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart14Model, v51, v52, v53] using newpart14_run ({s with memory := v19}) (v50) (v49) (v48) (v45) (v44) (v42) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h15 : runInstructions newpart15Program {s with pc := N 8293, memory := v19, stack := v53 :: v52 :: v45 :: v51 :: v50 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8301, memory := v19, stack := v58 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart15Model, v54, v55, v56, v57, v58] using newpart15_run ({s with memory := v19}) (v53) (v52) (v45) (v51) (v50) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h16 : runInstructions newpart16Program {s with pc := N 8301, memory := v19, stack := v58 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8310, memory := v19, stack := v62 :: v60 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart16Model, v59, v60, v61, v62] using newpart16_run ({s with memory := v19}) (v58) (v54) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h17 : runInstructions newpart17Program {s with pc := N 8310, memory := v19, stack := v62 :: v60 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8320, memory := v19, stack := v67 :: w11 :: v66 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart17Model, v63, v64, v65, v66, v67] using newpart17_run ({s with memory := v19}) (v62) (v60) (v54) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h18 : runInstructions newpart18Program {s with pc := N 8320, memory := v19, stack := v67 :: w11 :: v66 :: v54 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8328, memory := v19, stack := v71 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart18Model, v68, v69, v70, v71] using newpart18_run ({s with memory := v19}) (v67) (w11) (v66) (v54) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h19 : runInstructions newpart19Program {s with pc := N 8328, memory := v19, stack := v71 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8338, memory := v19, stack := v74 :: w14 :: w9 :: v73 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart19Model, v72, v73, v74] using newpart19_run ({s with memory := v19}) (v71) (v69) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h20 : runInstructions newpart20Program {s with pc := N 8338, memory := v19, stack := v74 :: w14 :: w9 :: v73 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8346, memory := v19, stack := v79 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart20Model, v75, v76, v77, v78, v79] using newpart20_run ({s with memory := v19}) (v74) (w14) (w9) (v73) (v69) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h21 : runInstructions newpart21Program {s with pc := N 8346, memory := v19, stack := v79 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8355, memory := v19, stack := w13 :: w9 :: v82 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart21Model, v80, v81, v82] using newpart21_run ({s with memory := v19}) (v79) (v69) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h22 : runInstructions newpart22Program {s with pc := N 8355, memory := v19, stack := w13 :: w9 :: v82 :: v69 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8365, memory := v19, stack := v85 :: v85 :: w13 :: w9 :: v82 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart22Model, v83, v84, v85] using newpart22_run ({s with memory := v19}) (w13) (w9) (v82) (v69) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h23 : runInstructions newpart23Program {s with pc := N 8365, memory := v19, stack := v85 :: v85 :: w13 :: w9 :: v82 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8379, memory := v86, stack := v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart23Model, v86, v87, v88, v89, v90] using newpart23_run ({s with memory := v19}) (v85) (v85) (w13) (w9) (v82) (w9) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h24 : runInstructions newpart24Program {s with pc := N 8379, memory := v86, stack := v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8391, memory := v86, stack := v93 :: v92 :: v91 :: v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart24Model, v91, v92, v93] using newpart24_run ({s with memory := v86}) (v90) (v89) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h25 : runInstructions newpart25Program {s with pc := N 8391, memory := v86, stack := v93 :: v92 :: v91 :: v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8399, memory := v86, stack := v96 :: v95 :: v93 :: v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart25Model, v94, v95, v96] using newpart25_run ({s with memory := v86}) (v93) (v92) (v91) (v90) (v89) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h26 : runInstructions newpart26Program {s with pc := N 8399, memory := v86, stack := v96 :: v95 :: v93 :: v90 :: v89 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8407, memory := v86, stack := w9 :: v100 :: v98 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart26Model, v97, v98, v99, v100] using newpart26_run ({s with memory := v86}) (v96) (v95) (v93) (v90) (v89) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h27 : runInstructions newpart27Program {s with pc := N 8407, memory := v86, stack := w9 :: v100 :: v98 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8417, memory := v86, stack := v103 :: w6 :: w9 :: v100 :: v101 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart27Model, v101, v102, v103] using newpart27_run ({s with memory := v86}) (w9) (v100) (v98) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h28 : runInstructions newpart28Program {s with pc := N 8417, memory := v86, stack := v103 :: w6 :: w9 :: v100 :: v101 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8428, memory := v86, stack := v107 :: v106 :: w9 :: v105 :: v103 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart28Model, v104, v105, v106, v107] using newpart28_run ({s with memory := v86}) (v103) (w6) (w9) (v100) (v101) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h29 : runInstructions newpart29Program {s with pc := N 8428, memory := v86, stack := v107 :: v106 :: w9 :: v105 :: v103 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8436, memory := v86, stack := v111 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart29Model, v108, v109, v110, v111] using newpart29_run ({s with memory := v86}) (v107) (v106) (w9) (v105) (v103) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h30 : runInstructions newpart30Program {s with pc := N 8436, memory := v86, stack := v111 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8447, memory := v86, stack := v113 :: v112 :: v109 :: v112 :: w9 :: v111 :: v113 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart30Model, v112, v113] using newpart30_run ({s with memory := v86}) (v111) (v109) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h31 : runInstructions newpart31Program {s with pc := N 8447, memory := v86, stack := v113 :: v112 :: v109 :: v112 :: w9 :: v111 :: v113 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8458, memory := v86, stack := v119 :: v118 :: v117 :: v115 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart31Model, v114, v115, v116, v117, v118, v119] using newpart31_run ({s with memory := v86}) (v113) (v112) (v109) (v112) (w9) (v111) (v113) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h32 : runInstructions newpart32Program {s with pc := N 8458, memory := v86, stack := v119 :: v118 :: v117 :: v115 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8468, memory := v86, stack := v122 :: v121 :: v118 :: v117 :: v115 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart32Model, v120, v121, v122] using newpart32_run ({s with memory := v86}) (v119) (v118) (v117) (v115) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h33 : runInstructions newpart33Program {s with pc := N 8468, memory := v86, stack := v122 :: v121 :: v118 :: v117 :: v115 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8478, memory := v86, stack := v118 :: w9 :: v125 :: v118 :: v124 :: v123 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart33Model, v123, v124, v125] using newpart33_run ({s with memory := v86}) (v122) (v121) (v118) (v117) (v115) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h34 : runInstructions newpart34Program {s with pc := N 8478, memory := v86, stack := v118 :: w9 :: v125 :: v118 :: v124 :: v123 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8486, memory := v86, stack := w10 :: w3 :: v129 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart34Model, v126, v127, v128, v129] using newpart34_run ({s with memory := v86}) (v118) (w9) (v125) (v118) (v124) (v123) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h35 : runInstructions newpart35Program {s with pc := N 8486, memory := v86, stack := w10 :: w3 :: v129 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8496, memory := v86, stack := v134 :: w4 :: v133 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart35Model, v130, v131, v132, v133, v134] using newpart35_run ({s with memory := v86}) (w10) (w3) (v129) (v127) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h36 : runInstructions newpart36Program {s with pc := N 8496, memory := v86, stack := v134 :: w4 :: v133 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8504, memory := v86, stack := w2 :: v139 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart36Model, v135, v136, v137, v138, v139] using newpart36_run ({s with memory := v86}) (v134) (w4) (v133) (v127) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h37 : runInstructions newpart37Program {s with pc := N 8504, memory := v86, stack := w2 :: v139 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8515, memory := v86, stack := v144 :: v142 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart37Model, v140, v141, v142, v143, v144] using newpart37_run ({s with memory := v86}) (w2) (v139) (v127) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h38 : runInstructions newpart38Program {s with pc := N 8515, memory := v86, stack := v144 :: v142 :: v127 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8523, memory := v86, stack := w9 :: v147 :: v145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart38Model, v145, v146, v147] using newpart38_run ({s with memory := v86}) (v144) (v142) (v127) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h39 : runInstructions newpart39Program {s with pc := N 8523, memory := v86, stack := w9 :: v147 :: v145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 8529, memory := v86, stack := w4 :: w9 :: v149 :: v145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart39Model, v148, v149] using newpart39_run ({s with memory := v86}) (w9) (v147) (v145) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 (runInstructions_append_some _ _ _ _ _ h21 (runInstructions_append_some _ _ _ _ _ h22 (runInstructions_append_some _ _ _ _ _ h23 (runInstructions_append_some _ _ _ _ _ h24 (runInstructions_append_some _ _ _ _ _ h25 (runInstructions_append_some _ _ _ _ _ h26 (runInstructions_append_some _ _ _ _ _ h27 (runInstructions_append_some _ _ _ _ _ h28 (runInstructions_append_some _ _ _ _ _ h29 (runInstructions_append_some _ _ _ _ _ h30 (runInstructions_append_some _ _ _ _ _ h31 (runInstructions_append_some _ _ _ _ _ h32 (runInstructions_append_some _ _ _ _ _ h33 (runInstructions_append_some _ _ _ _ _ h34 (runInstructions_append_some _ _ _ _ _ h35 (runInstructions_append_some _ _ _ _ _ h36 (runInstructions_append_some _ _ _ _ _ h37 (runInstructions_append_some _ _ _ _ _ h38 h39)))))))))))))))))))))))))))))))))))))))

#print axioms new_run

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 224) 192) = (MachineState.readWord s.memory 192) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 224) 0) = (MachineState.readWord s.memory 0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (s : State) (w12 : W) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (UInt256.land w12 z0).toNat 32) 224) 224) = (UInt256.land w12 z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 224) 2720) = (MachineState.readWord s.memory 2720) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 768) = (MachineState.readWord z0 768) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1952) = (MachineState.readWord z0 1952) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared6 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1920) = (MachineState.readWord z0 1920) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared7 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 32) = (MachineState.readWord z0 32) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared8 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1888) = (MachineState.readWord z0 1888) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared9 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 64) = (MachineState.readWord z0 64) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared10 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1856) = (MachineState.readWord z0 1856) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared11 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 96) = (MachineState.readWord z0 96) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared12 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1824) = (MachineState.readWord z0 1824) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared13 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 1792) = (MachineState.readWord z0 1792) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared14 (s : State) (z0 z1 : W) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 224) (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 192) = (MachineState.readWord s.memory 192) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared15 (s : State) (z0 z1 : W) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 224) (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 0) = (MachineState.readWord s.memory 0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared16 (s : State) (w12 : W) (z0 z1 : W) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (UInt256.land w12 z0).toNat 32) 224) (Data.Bytes.natToBytesPadded z1.toNat 32) 1216) 224) = (UInt256.land w12 z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared17 (w12 : W) (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded (UInt256.land w12 z1).toNat 32) 1216) 1216) = (UInt256.land w12 z1) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared18 (w9 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w9) = (UInt256.mulMod z1 z0 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared19 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared20 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared21 (w5 w9 : W) (z0 : W) :
    (UInt256.mulMod w5 z0 w9) = (UInt256.mulMod z0 w5 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared22 (w5 : W) (z0 : W) :
    (w5 * z0) = (z0 * w5) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

theorem same_state (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := MachineState.readWord s.memory 192
  let o1 : W := o0 * carry
  let o2 : W := o1 + w0
  let o3 : W := MachineState.readWord s.memory 0
  let o4 : W := o3 * w11
  let o5 : W := o4 + o2
  let o6 : W := UInt256.mulMod w10 w4 w9
  let o7 : W := o6 + w1
  let o8 : W := UInt256.mulMod w8 w14 w9
  let o9 : W := o8 + o7
  let o10 : W := MachineState.readWord s.memory 192
  let o11 : W := UInt256.mulMod o10 w2 w9
  let o12 : W := o11 + o9
  let o13 : W := MachineState.readWord s.memory 0
  let o14 : W := UInt256.mulMod o13 w11 w9
  let o15 : W := o14 + o12
  let o16 : W := MachineState.readWord s.memory 2720
  let o17 : W := o5 * o16
  let o18 : W := UInt256.land w12 o17
  let o19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o18.toNat 32) 224
  let o20 : W := UInt256.mulMod o18 w13 w9
  let o21 : W := o20 + o15
  let o22 : W := UInt256.mulMod (N 2048) o21 w9
  let o23 : W := MachineState.readWord o19 768
  let o24 : W := MachineState.readWord o19 1952
  let o25 : W := o24 * o23
  let o26 : W := o25 + o22
  let o27 : W := UInt256.mulMod o24 o23 w9
  let o28 : W := o27 + o22
  let o29 : W := MachineState.readWord o19 1920
  let o30 : W := o29 * w5
  let o31 : W := o30 + o26
  let o32 : W := UInt256.mulMod o29 w5 w9
  let o33 : W := o32 + o28
  let o34 : W := MachineState.readWord o19 1888
  let o35 : W := o34 * w6
  let o36 : W := o35 + o31
  let o37 : W := UInt256.mulMod o34 w6 w9
  let o38 : W := o37 + o33
  let o39 : W := MachineState.readWord o19 32
  let o40 : W := MachineState.readWord o19 1856
  let o41 : W := o40 * o39
  let o42 : W := o41 + o36
  let o43 : W := UInt256.mulMod o40 o39 w9
  let o44 : W := o43 + o38
  let o45 : W := MachineState.readWord o19 64
  let o46 : W := MachineState.readWord o19 1824
  let o47 : W := o46 * o45
  let o48 : W := o47 + o42
  let o49 : W := UInt256.mulMod o46 o45 w9
  let o50 : W := o49 + o44
  let o51 : W := MachineState.readWord o19 96
  let o52 : W := MachineState.readWord o19 1792
  let o53 : W := o52 * o51
  let o54 : W := o53 + o48
  let o55 : W := UInt256.mulMod o52 o51 w9
  let o56 : W := o55 + o50
  let o57 : W := w10 * w7
  let o58 : W := o57 + o54
  let o59 : W := w8 * w4
  let o60 : W := o59 + o58
  let o61 : W := MachineState.readWord o19 192
  let o62 : W := o61 * w14
  let o63 : W := o62 + o60
  let o64 : W := MachineState.readWord o19 0
  let o65 : W := o64 * w2
  let o66 : W := o65 + o63
  let o67 : W := MachineState.readWord o19 224
  let o68 : W := o67 * w11
  let o69 : W := o68 + o66
  let o70 : W := UInt256.mulMod w10 w7 w9
  let o71 : W := o70 + o56
  let o72 : W := UInt256.mulMod w8 w4 w9
  let o73 : W := o72 + o71
  let o74 : W := MachineState.readWord o19 192
  let o75 : W := UInt256.mulMod o74 w14 w9
  let o76 : W := o75 + o73
  let o77 : W := MachineState.readWord o19 0
  let o78 : W := UInt256.mulMod o77 w2 w9
  let o79 : W := o78 + o76
  let o80 : W := MachineState.readWord o19 224
  let o81 : W := UInt256.mulMod o80 w11 w9
  let o82 : W := o81 + o79
  let o83 : W := MachineState.readWord o19 2720
  let o84 : W := o69 * o83
  let o85 : W := UInt256.land w12 o84
  let o86 : ByteArray := MachineState.writeBytes o19 (Data.Bytes.natToBytesPadded o85.toNat 32) 1216
  let o87 : W := UInt256.mulMod o85 w13 w9
  let o88 : W := o87 + o82
  let o89 : W := UInt256.mulMod (N 2048) o88 w9
  let o90 : W := MachineState.readWord o86 768
  let o91 : W := MachineState.readWord o86 1984
  let o92 : W := o91 * o90
  let o93 : W := o92 + o89
  let o94 : W := UInt256.mulMod o91 o90 w9
  let o95 : W := o94 + o89
  let o96 : W := MachineState.readWord o86 1952
  let o97 : W := o96 * w5
  let o98 : W := o97 + o93
  let o99 : W := UInt256.mulMod o96 w5 w9
  let o100 : W := o99 + o95
  let o101 : W := MachineState.readWord o86 1920
  let o102 : W := o101 * w6
  let o103 : W := o102 + o98
  let o104 : W := UInt256.mulMod o101 w6 w9
  let o105 : W := o104 + o100
  let o106 : W := MachineState.readWord o86 32
  let o107 : W := MachineState.readWord o86 1888
  let o108 : W := o107 * o106
  let o109 : W := o108 + o103
  let o110 : W := UInt256.mulMod o107 o106 w9
  let o111 : W := o110 + o105
  let o112 : W := MachineState.readWord o86 64
  let o113 : W := MachineState.readWord o86 1856
  let o114 : W := o113 * o112
  let o115 : W := o114 + o109
  let o116 : W := UInt256.mulMod o113 o112 w9
  let o117 : W := o116 + o111
  let o118 : W := MachineState.readWord o86 96
  let o119 : W := MachineState.readWord o86 1824
  let o120 : W := o119 * o118
  let o121 : W := o120 + o115
  let o122 : W := UInt256.mulMod o119 o118 w9
  let o123 : W := o122 + o117
  let o124 : W := MachineState.readWord o86 128
  let o125 : W := MachineState.readWord o86 1792
  let o126 : W := o125 * o124
  let o127 : W := o126 + o121
  let o128 : W := UInt256.mulMod o125 o124 w9
  let o129 : W := o128 + o123
  let o130 : W := w10 * w3
  let o131 : W := o130 + o127
  let o132 : W := w8 * w7
  let o133 : W := o132 + o131
  let o134 : W := MachineState.readWord o86 192
  let o135 : W := o134 * w4
  let o136 : W := o135 + o133
  let o137 : W := MachineState.readWord o86 0
  let o138 : W := o137 * w14
  let o139 : W := o138 + o136
  let o140 : W := MachineState.readWord o86 224
  let o141 : W := o140 * w2
  let o142 : W := o141 + o139
  let o143 : W := MachineState.readWord o86 1216
  let o144 : W := o143 * w11
  let o145 : W := o144 + o142
  let o146 : W := UInt256.mulMod w10 w3 w9
  let o147 : W := o146 + o129
  let o148 : W := UInt256.mulMod w8 w7 w9
  let o149 : W := o148 + o147
  let n0 : W := MachineState.readWord s.memory 192
  let n1 : W := n0 * carry
  let n2 : W := n1 + w0
  let n3 : W := MachineState.readWord s.memory 0
  let n4 : W := n3 * w11
  let n5 : W := n4 + n2
  let n6 : W := UInt256.mulMod w10 w4 w9
  let n7 : W := n6 + w1
  let n8 : W := UInt256.mulMod w8 w14 w9
  let n9 : W := n8 + n7
  let n10 : W := MachineState.readWord s.memory 192
  let n11 : W := UInt256.mulMod n10 w2 w9
  let n12 : W := n11 + n9
  let n13 : W := MachineState.readWord s.memory 0
  let n14 : W := UInt256.mulMod n13 w11 w9
  let n15 : W := n14 + n12
  let n16 : W := MachineState.readWord s.memory 2720
  let n17 : W := n5 * n16
  let n18 : W := UInt256.land w12 n17
  let n19 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n18.toNat 32) 224
  let n20 : W := UInt256.mulMod n18 w13 w9
  let n21 : W := n20 + n15
  let n22 : W := UInt256.mulMod (N 2048) n21 w9
  let n23 : W := MachineState.readWord n19 1920
  let n24 : W := MachineState.readWord n19 768
  let n25 : W := MachineState.readWord n19 1952
  let n26 : W := UInt256.mulMod n24 n25 w9
  let n27 : W := n24 * n25
  let n28 : W := n22 + n27
  let n29 : W := UInt256.mulMod w5 n23 w9
  let n30 : W := w5 * n23
  let n31 : W := n30 + n28
  let n32 : W := n22 + n26
  let n33 : W := n32 + n29
  let n34 : W := MachineState.readWord n19 1888
  let n35 : W := n34 * w6
  let n36 : W := n35 + n31
  let n37 : W := UInt256.mulMod n34 w6 w9
  let n38 : W := n37 + n33
  let n39 : W := MachineState.readWord n19 32
  let n40 : W := MachineState.readWord n19 1856
  let n41 : W := n40 * n39
  let n42 : W := n41 + n36
  let n43 : W := UInt256.mulMod n40 n39 w9
  let n44 : W := n43 + n38
  let n45 : W := MachineState.readWord n19 96
  let n46 : W := MachineState.readWord n19 64
  let n47 : W := MachineState.readWord n19 1824
  let n48 : W := UInt256.mulMod n46 n47 w9
  let n49 : W := n46 * n47
  let n50 : W := MachineState.readWord n19 1792
  let n51 : W := n42 + n49
  let n52 : W := n44 + n48
  let n53 : W := UInt256.mulMod n50 n45 w9
  let n54 : W := n53 + n52
  let n55 : W := n50 * n45
  let n56 : W := n55 + n51
  let n57 : W := w10 * w7
  let n58 : W := n57 + n56
  let n59 : W := w8 * w4
  let n60 : W := n59 + n58
  let n61 : W := MachineState.readWord n19 192
  let n62 : W := n61 * w14
  let n63 : W := n62 + n60
  let n64 : W := MachineState.readWord n19 0
  let n65 : W := n64 * w2
  let n66 : W := n65 + n63
  let n67 : W := MachineState.readWord n19 224
  let n68 : W := n67 * w11
  let n69 : W := n68 + n66
  let n70 : W := UInt256.mulMod w10 w7 w9
  let n71 : W := n70 + n54
  let n72 : W := UInt256.mulMod w8 w4 w9
  let n73 : W := n72 + n71
  let n74 : W := MachineState.readWord n19 192
  let n75 : W := UInt256.mulMod n74 w14 w9
  let n76 : W := n75 + n73
  let n77 : W := MachineState.readWord n19 0
  let n78 : W := UInt256.mulMod n77 w2 w9
  let n79 : W := n78 + n76
  let n80 : W := MachineState.readWord n19 224
  let n81 : W := UInt256.mulMod n80 w11 w9
  let n82 : W := n81 + n79
  let n83 : W := MachineState.readWord n19 2720
  let n84 : W := n69 * n83
  let n85 : W := UInt256.land w12 n84
  let n86 : ByteArray := MachineState.writeBytes n19 (Data.Bytes.natToBytesPadded n85.toNat 32) 1216
  let n87 : W := UInt256.mulMod n85 w13 w9
  let n88 : W := n87 + n82
  let n89 : W := UInt256.mulMod (N 2048) n88 w9
  let n90 : W := MachineState.readWord n86 1952
  let n91 : W := MachineState.readWord n86 768
  let n92 : W := MachineState.readWord n86 1984
  let n93 : W := UInt256.mulMod n91 n92 w9
  let n94 : W := n91 * n92
  let n95 : W := n89 + n94
  let n96 : W := UInt256.mulMod w5 n90 w9
  let n97 : W := w5 * n90
  let n98 : W := n97 + n95
  let n99 : W := n89 + n93
  let n100 : W := n99 + n96
  let n101 : W := MachineState.readWord n86 1920
  let n102 : W := n101 * w6
  let n103 : W := n102 + n98
  let n104 : W := UInt256.mulMod n101 w6 w9
  let n105 : W := n104 + n100
  let n106 : W := MachineState.readWord n86 32
  let n107 : W := MachineState.readWord n86 1888
  let n108 : W := n107 * n106
  let n109 : W := n108 + n103
  let n110 : W := UInt256.mulMod n107 n106 w9
  let n111 : W := n110 + n105
  let n112 : W := MachineState.readWord n86 64
  let n113 : W := MachineState.readWord n86 1856
  let n114 : W := n113 * n112
  let n115 : W := n114 + n109
  let n116 : W := UInt256.mulMod n113 n112 w9
  let n117 : W := n116 + n111
  let n118 : W := MachineState.readWord n86 128
  let n119 : W := MachineState.readWord n86 96
  let n120 : W := MachineState.readWord n86 1824
  let n121 : W := UInt256.mulMod n119 n120 w9
  let n122 : W := n119 * n120
  let n123 : W := MachineState.readWord n86 1792
  let n124 : W := n115 + n122
  let n125 : W := n117 + n121
  let n126 : W := UInt256.mulMod n123 n118 w9
  let n127 : W := n126 + n125
  let n128 : W := n123 * n118
  let n129 : W := n128 + n124
  let n130 : W := w10 * w3
  let n131 : W := n130 + n129
  let n132 : W := w8 * w7
  let n133 : W := n132 + n131
  let n134 : W := MachineState.readWord n86 192
  let n135 : W := n134 * w4
  let n136 : W := n135 + n133
  let n137 : W := MachineState.readWord n86 0
  let n138 : W := n137 * w14
  let n139 : W := n138 + n136
  let n140 : W := MachineState.readWord n86 224
  let n141 : W := n140 * w2
  let n142 : W := n141 + n139
  let n143 : W := MachineState.readWord n86 1216
  let n144 : W := n143 * w11
  let n145 : W := n144 + n142
  let n146 : W := UInt256.mulMod w10 w3 w9
  let n147 : W := n146 + n127
  let n148 : W := UInt256.mulMod w8 w7 w9
  let n149 : W := n148 + n147
  have eq_o10 : o10 = o0 := by
    simp only [o10, o0]
  have eq_o13 : o13 = o3 := by
    simp only [o13, o3]
  have eq_o61 : o61 = o0 := by
    simpa only [o61, o19, o0] using
      (aux_shared0 s  o18)
  have eq_o64 : o64 = o3 := by
    simpa only [o64, o19, o3] using
      (aux_shared1 s  o18)
  have eq_o67 : o67 = o18 := by
    simpa only [o67, o19, o18] using
      (aux_shared2 s w12 o17)
  have eq_o74 : o74 = o0 := by
    simpa only [o74, o19, o0] using
      (aux_shared0 s  o18)
  have eq_o77 : o77 = o3 := by
    simpa only [o77, o19, o3] using
      (aux_shared1 s  o18)
  have eq_o80 : o80 = o18 := by
    simpa only [o80, o19, o18] using
      (aux_shared2 s w12 o17)
  have eq_o83 : o83 = o16 := by
    simpa only [o83, o19, o16] using
      (aux_shared3 s  o18)
  have eq_o90 : o90 = o23 := by
    simpa only [o90, o86, o23] using
      (aux_shared4  o85 o19)
  have eq_o96 : o96 = o24 := by
    simpa only [o96, o86, o24] using
      (aux_shared5  o85 o19)
  have eq_o101 : o101 = o29 := by
    simpa only [o101, o86, o29] using
      (aux_shared6  o85 o19)
  have eq_o106 : o106 = o39 := by
    simpa only [o106, o86, o39] using
      (aux_shared7  o85 o19)
  have eq_o107 : o107 = o34 := by
    simpa only [o107, o86, o34] using
      (aux_shared8  o85 o19)
  have eq_o112 : o112 = o45 := by
    simpa only [o112, o86, o45] using
      (aux_shared9  o85 o19)
  have eq_o113 : o113 = o40 := by
    simpa only [o113, o86, o40] using
      (aux_shared10  o85 o19)
  have eq_o118 : o118 = o51 := by
    simpa only [o118, o86, o51] using
      (aux_shared11  o85 o19)
  have eq_o119 : o119 = o46 := by
    simpa only [o119, o86, o46] using
      (aux_shared12  o85 o19)
  have eq_o125 : o125 = o52 := by
    simpa only [o125, o86, o52] using
      (aux_shared13  o85 o19)
  have eq_o134 : o134 = o0 := by
    simpa only [o134, o86, o19, o0] using
      (aux_shared14 s  o18 o85)
  have eq_o137 : o137 = o3 := by
    simpa only [o137, o86, o19, o3] using
      (aux_shared15 s  o18 o85)
  have eq_o140 : o140 = o18 := by
    simpa only [o140, o86, o19, o18] using
      (aux_shared16 s w12 o17 o85)
  have eq_o143 : o143 = o85 := by
    simpa only [o143, o86, o85] using
      (aux_shared17 w12 o84 o19)
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2, eq_n1]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4, eq_n3]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4, eq_n2]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7, eq_n6]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8, eq_n7]
  have eq_n10 : n10 = o0 := by
    simp only [n10, o0]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n10, eq_o10]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12, eq_n11, eq_n9]
  have eq_n13 : n13 = o3 := by
    simp only [n13, o3]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14, eq_n13, eq_o13]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14, eq_n12]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n5, eq_n16]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n17]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n18]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n18]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20, eq_n15]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22, eq_n21]
  have eq_n23 : n23 = o29 := by
    simp only [n23, o29, eq_n19]
  have eq_n24 : n24 = o23 := by
    simp only [n24, o23, eq_n19]
  have eq_n25 : n25 = o24 := by
    simp only [n25, o24, eq_n19]
  have eq_n26 : n26 = o27 := by
    simpa only [n26, o27, eq_n24, eq_n25] using
      (aux_shared18 w9 o23 o24)
  have eq_n27 : n27 = o25 := by
    simpa only [n27, o25, eq_n24, eq_n25] using
      (aux_shared19  o23 o24)
  have eq_n28 : n28 = o26 := by
    simpa only [n28, o26, eq_n22, eq_n27] using
      (aux_shared20  o22 o25)
  have eq_n29 : n29 = o32 := by
    simpa only [n29, o32, eq_n23] using
      (aux_shared21 w5 w9 o29)
  have eq_n30 : n30 = o30 := by
    simpa only [n30, o30, eq_n23] using
      (aux_shared22 w5 o29)
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n30, eq_n28]
  have eq_n32 : n32 = o28 := by
    simpa only [n32, o28, eq_n22, eq_n26] using
      (aux_shared20  o22 o27)
  have eq_n33 : n33 = o33 := by
    simpa only [n33, o33, eq_n32, eq_n29] using
      (aux_shared20  o28 o32)
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n19]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n34]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n35, eq_n31]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n34]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37, eq_n33]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n19]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n19]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n40, eq_n39]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n41, eq_n36]
  have eq_n43 : n43 = o43 := by
    simp only [n43, o43, eq_n40, eq_n39]
  have eq_n44 : n44 = o44 := by
    simp only [n44, o44, eq_n43, eq_n38]
  have eq_n45 : n45 = o51 := by
    simp only [n45, o51, eq_n19]
  have eq_n46 : n46 = o45 := by
    simp only [n46, o45, eq_n19]
  have eq_n47 : n47 = o46 := by
    simp only [n47, o46, eq_n19]
  have eq_n48 : n48 = o49 := by
    simpa only [n48, o49, eq_n46, eq_n47] using
      (aux_shared18 w9 o45 o46)
  have eq_n49 : n49 = o47 := by
    simpa only [n49, o47, eq_n46, eq_n47] using
      (aux_shared19  o45 o46)
  have eq_n50 : n50 = o52 := by
    simp only [n50, o52, eq_n19]
  have eq_n51 : n51 = o48 := by
    simpa only [n51, o48, eq_n42, eq_n49] using
      (aux_shared20  o42 o47)
  have eq_n52 : n52 = o50 := by
    simpa only [n52, o50, eq_n44, eq_n48] using
      (aux_shared20  o44 o49)
  have eq_n53 : n53 = o55 := by
    simp only [n53, o55, eq_n50, eq_n45]
  have eq_n54 : n54 = o56 := by
    simp only [n54, o56, eq_n53, eq_n52]
  have eq_n55 : n55 = o53 := by
    simp only [n55, o53, eq_n50, eq_n45]
  have eq_n56 : n56 = o54 := by
    simp only [n56, o54, eq_n55, eq_n51]
  have eq_n57 : n57 = o57 := by
    simp only [n57, o57]
  have eq_n58 : n58 = o58 := by
    simp only [n58, o58, eq_n57, eq_n56]
  have eq_n59 : n59 = o59 := by
    simp only [n59, o59]
  have eq_n60 : n60 = o60 := by
    simp only [n60, o60, eq_n59, eq_n58]
  have eq_n61 : n61 = o0 := by
    simpa only [n61, n19, o0, eq_n18] using
      (aux_shared0 s  o18)
  have eq_n62 : n62 = o62 := by
    simp only [n62, o62, eq_n61, eq_o61]
  have eq_n63 : n63 = o63 := by
    simp only [n63, o63, eq_n62, eq_n60]
  have eq_n64 : n64 = o3 := by
    simpa only [n64, n19, o3, eq_n18] using
      (aux_shared1 s  o18)
  have eq_n65 : n65 = o65 := by
    simp only [n65, o65, eq_n64, eq_o64]
  have eq_n66 : n66 = o66 := by
    simp only [n66, o66, eq_n65, eq_n63]
  have eq_n67 : n67 = o18 := by
    simpa only [n67, n19, n18, o18, eq_n17] using
      (aux_shared2 s w12 o17)
  have eq_n68 : n68 = o68 := by
    simp only [n68, o68, eq_n67, eq_o67]
  have eq_n69 : n69 = o69 := by
    simp only [n69, o69, eq_n68, eq_n66]
  have eq_n70 : n70 = o70 := by
    simp only [n70, o70]
  have eq_n71 : n71 = o71 := by
    simp only [n71, o71, eq_n70, eq_n54]
  have eq_n72 : n72 = o72 := by
    simp only [n72, o72]
  have eq_n73 : n73 = o73 := by
    simp only [n73, o73, eq_n72, eq_n71]
  have eq_n74 : n74 = o0 := by
    simpa only [n74, n19, o0, eq_n18] using
      (aux_shared0 s  o18)
  have eq_n75 : n75 = o75 := by
    simp only [n75, o75, eq_n74, eq_o74]
  have eq_n76 : n76 = o76 := by
    simp only [n76, o76, eq_n75, eq_n73]
  have eq_n77 : n77 = o3 := by
    simpa only [n77, n19, o3, eq_n18] using
      (aux_shared1 s  o18)
  have eq_n78 : n78 = o78 := by
    simp only [n78, o78, eq_n77, eq_o77]
  have eq_n79 : n79 = o79 := by
    simp only [n79, o79, eq_n78, eq_n76]
  have eq_n80 : n80 = o18 := by
    simpa only [n80, n19, n18, o18, eq_n17] using
      (aux_shared2 s w12 o17)
  have eq_n81 : n81 = o81 := by
    simp only [n81, o81, eq_n80, eq_o80]
  have eq_n82 : n82 = o82 := by
    simp only [n82, o82, eq_n81, eq_n79]
  have eq_n83 : n83 = o16 := by
    simpa only [n83, n19, o16, eq_n18] using
      (aux_shared3 s  o18)
  have eq_n84 : n84 = o84 := by
    simp only [n84, o84, eq_n69, eq_n83, eq_o83]
  have eq_n85 : n85 = o85 := by
    simp only [n85, o85, eq_n84]
  have eq_n86 : n86 = o86 := by
    simp only [n86, o86, eq_n19, eq_n85]
  have eq_n87 : n87 = o87 := by
    simp only [n87, o87, eq_n85]
  have eq_n88 : n88 = o88 := by
    simp only [n88, o88, eq_n87, eq_n82]
  have eq_n89 : n89 = o89 := by
    simp only [n89, o89, eq_n88]
  have eq_n90 : n90 = o24 := by
    simpa only [n90, n86, o24, eq_n19, eq_n85] using
      (aux_shared5  o85 o19)
  have eq_n91 : n91 = o23 := by
    simpa only [n91, n86, o23, eq_n19, eq_n85] using
      (aux_shared4  o85 o19)
  have eq_n92 : n92 = o91 := by
    simp only [n92, o91, eq_n86]
  have eq_n93 : n93 = o94 := by
    simpa only [n93, o94, eq_n91, eq_n92, eq_o90] using
      (aux_shared18 w9 o23 o91)
  have eq_n94 : n94 = o92 := by
    simpa only [n94, o92, eq_n91, eq_n92, eq_o90] using
      (aux_shared19  o23 o91)
  have eq_n95 : n95 = o93 := by
    simpa only [n95, o93, eq_n89, eq_n94] using
      (aux_shared20  o89 o92)
  have eq_n96 : n96 = o99 := by
    simpa only [n96, o99, eq_n90, eq_o96] using
      (aux_shared21 w5 w9 o24)
  have eq_n97 : n97 = o97 := by
    simpa only [n97, o97, eq_n90, eq_o96] using
      (aux_shared22 w5 o24)
  have eq_n98 : n98 = o98 := by
    simp only [n98, o98, eq_n97, eq_n95]
  have eq_n99 : n99 = o95 := by
    simpa only [n99, o95, eq_n89, eq_n93] using
      (aux_shared20  o89 o94)
  have eq_n100 : n100 = o100 := by
    simpa only [n100, o100, eq_n99, eq_n96] using
      (aux_shared20  o95 o99)
  have eq_n101 : n101 = o29 := by
    simpa only [n101, n86, o29, eq_n19, eq_n85] using
      (aux_shared6  o85 o19)
  have eq_n102 : n102 = o102 := by
    simp only [n102, o102, eq_n101, eq_o101]
  have eq_n103 : n103 = o103 := by
    simp only [n103, o103, eq_n102, eq_n98]
  have eq_n104 : n104 = o104 := by
    simp only [n104, o104, eq_n101, eq_o101]
  have eq_n105 : n105 = o105 := by
    simp only [n105, o105, eq_n104, eq_n100]
  have eq_n106 : n106 = o39 := by
    simpa only [n106, n86, o39, eq_n19, eq_n85] using
      (aux_shared7  o85 o19)
  have eq_n107 : n107 = o34 := by
    simpa only [n107, n86, o34, eq_n19, eq_n85] using
      (aux_shared8  o85 o19)
  have eq_n108 : n108 = o108 := by
    simp only [n108, o108, eq_n107, eq_n106, eq_o107, eq_o106]
  have eq_n109 : n109 = o109 := by
    simp only [n109, o109, eq_n108, eq_n103]
  have eq_n110 : n110 = o110 := by
    simp only [n110, o110, eq_n107, eq_n106, eq_o107, eq_o106]
  have eq_n111 : n111 = o111 := by
    simp only [n111, o111, eq_n110, eq_n105]
  have eq_n112 : n112 = o45 := by
    simpa only [n112, n86, o45, eq_n19, eq_n85] using
      (aux_shared9  o85 o19)
  have eq_n113 : n113 = o40 := by
    simpa only [n113, n86, o40, eq_n19, eq_n85] using
      (aux_shared10  o85 o19)
  have eq_n114 : n114 = o114 := by
    simp only [n114, o114, eq_n113, eq_n112, eq_o113, eq_o112]
  have eq_n115 : n115 = o115 := by
    simp only [n115, o115, eq_n114, eq_n109]
  have eq_n116 : n116 = o116 := by
    simp only [n116, o116, eq_n113, eq_n112, eq_o113, eq_o112]
  have eq_n117 : n117 = o117 := by
    simp only [n117, o117, eq_n116, eq_n111]
  have eq_n118 : n118 = o124 := by
    simp only [n118, o124, eq_n86]
  have eq_n119 : n119 = o51 := by
    simpa only [n119, n86, o51, eq_n19, eq_n85] using
      (aux_shared11  o85 o19)
  have eq_n120 : n120 = o46 := by
    simpa only [n120, n86, o46, eq_n19, eq_n85] using
      (aux_shared12  o85 o19)
  have eq_n121 : n121 = o122 := by
    simpa only [n121, o122, eq_n119, eq_n120, eq_o119, eq_o118] using
      (aux_shared18 w9 o51 o46)
  have eq_n122 : n122 = o120 := by
    simpa only [n122, o120, eq_n119, eq_n120, eq_o119, eq_o118] using
      (aux_shared19  o51 o46)
  have eq_n123 : n123 = o52 := by
    simpa only [n123, n86, o52, eq_n19, eq_n85] using
      (aux_shared13  o85 o19)
  have eq_n124 : n124 = o121 := by
    simpa only [n124, o121, eq_n115, eq_n122] using
      (aux_shared20  o115 o120)
  have eq_n125 : n125 = o123 := by
    simpa only [n125, o123, eq_n117, eq_n121] using
      (aux_shared20  o117 o122)
  have eq_n126 : n126 = o128 := by
    simp only [n126, o128, eq_n123, eq_n118, eq_o125]
  have eq_n127 : n127 = o129 := by
    simp only [n127, o129, eq_n126, eq_n125]
  have eq_n128 : n128 = o126 := by
    simp only [n128, o126, eq_n123, eq_n118, eq_o125]
  have eq_n129 : n129 = o127 := by
    simp only [n129, o127, eq_n128, eq_n124]
  have eq_n130 : n130 = o130 := by
    simp only [n130, o130]
  have eq_n131 : n131 = o131 := by
    simp only [n131, o131, eq_n130, eq_n129]
  have eq_n132 : n132 = o132 := by
    simp only [n132, o132]
  have eq_n133 : n133 = o133 := by
    simp only [n133, o133, eq_n132, eq_n131]
  have eq_n134 : n134 = o0 := by
    simpa only [n134, n86, n19, o0, eq_n18, eq_n85] using
      (aux_shared14 s  o18 o85)
  have eq_n135 : n135 = o135 := by
    simp only [n135, o135, eq_n134, eq_o134]
  have eq_n136 : n136 = o136 := by
    simp only [n136, o136, eq_n135, eq_n133]
  have eq_n137 : n137 = o3 := by
    simpa only [n137, n86, n19, o3, eq_n18, eq_n85] using
      (aux_shared15 s  o18 o85)
  have eq_n138 : n138 = o138 := by
    simp only [n138, o138, eq_n137, eq_o137]
  have eq_n139 : n139 = o139 := by
    simp only [n139, o139, eq_n138, eq_n136]
  have eq_n140 : n140 = o18 := by
    simpa only [n140, n86, n19, n18, o18, eq_n17, eq_n85] using
      (aux_shared16 s w12 o17 o85)
  have eq_n141 : n141 = o141 := by
    simp only [n141, o141, eq_n140, eq_o140]
  have eq_n142 : n142 = o142 := by
    simp only [n142, o142, eq_n141, eq_n139]
  have eq_n143 : n143 = o85 := by
    simpa only [n143, n86, n85, o85, eq_n19, eq_n84] using
      (aux_shared17 w12 o84 o19)
  have eq_n144 : n144 = o144 := by
    simp only [n144, o144, eq_n143, eq_o143]
  have eq_n145 : n145 = o145 := by
    simp only [n145, o145, eq_n144, eq_n142]
  have eq_n146 : n146 = o146 := by
    simp only [n146, o146]
  have eq_n147 : n147 = o147 := by
    simp only [n147, o147, eq_n146, eq_n127]
  have eq_n148 : n148 = o148 := by
    simp only [n148, o148]
  have eq_n149 : n149 = o149 := by
    simp only [n149, o149, eq_n148, eq_n147]
  change {s with pc := N 8529, memory := o86, stack := w4 :: w9 :: o149 :: o145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
    {s with pc := N 8529, memory := n86, stack := w4 :: w9 :: n149 :: n145 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}
  simp only [eq_o10, eq_o13, eq_o61, eq_o64, eq_o67, eq_o74, eq_o77, eq_o80, eq_o83, eq_o90, eq_o96, eq_o101, eq_o106, eq_o107, eq_o112, eq_o113, eq_o118, eq_o119, eq_o125, eq_o134, eq_o137, eq_o140, eq_o143, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52, eq_n53, eq_n54, eq_n55, eq_n56, eq_n57, eq_n58, eq_n59, eq_n60, eq_n61, eq_n62, eq_n63, eq_n64, eq_n65, eq_n66, eq_n67, eq_n68, eq_n69, eq_n70, eq_n71, eq_n72, eq_n73, eq_n74, eq_n75, eq_n76, eq_n77, eq_n78, eq_n79, eq_n80, eq_n81, eq_n82, eq_n83, eq_n84, eq_n85, eq_n86, eq_n87, eq_n88, eq_n89, eq_n90, eq_n91, eq_n92, eq_n93, eq_n94, eq_n95, eq_n96, eq_n97, eq_n98, eq_n99, eq_n100, eq_n101, eq_n102, eq_n103, eq_n104, eq_n105, eq_n106, eq_n107, eq_n108, eq_n109, eq_n110, eq_n111, eq_n112, eq_n113, eq_n114, eq_n115, eq_n116, eq_n117, eq_n118, eq_n119, eq_n120, eq_n121, eq_n122, eq_n123, eq_n124, eq_n125, eq_n126, eq_n127, eq_n128, eq_n129, eq_n130, eq_n131, eq_n132, eq_n133, eq_n134, eq_n135, eq_n136, eq_n137, eq_n138, eq_n139, eq_n140, eq_n141, eq_n142, eq_n143, eq_n144, eq_n145, eq_n146, eq_n147, eq_n148, eq_n149]

def eval3 (s : State) : State :=
  productColumn3Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack.drop 17)

def eval4 (s : State) : State :=
  productColumn4Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack[17]!) (s.stack[18]!) (s.stack[19]!) (s.stack[20]!) (s.stack.drop 21)

def eval5 (s : State) : State :=
  productColumn5Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack[17]!) (s.stack[18]!) (s.stack[19]!) (s.stack.drop 20)

theorem old_eval (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = eval5 (eval4 (eval3 ({s with pc := N 8149, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}))) := by
  rfl

#print axioms old_eval
#print axioms new_run
#print axioms same_state
end CycleSubmission.Prepared.ProductGroup8130

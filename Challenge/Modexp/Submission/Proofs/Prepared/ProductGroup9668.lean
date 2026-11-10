import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product15
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product16
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product17
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
namespace CycleSubmission.Prepared.ProductGroup9668
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast


open CycleSubmission.Prepared.Arithmetic CycleSubmission.Execution
open Challenge.EvmProof.Word Challenge.EvmProof.Stepper
local notation "W" => UInt256
local notation "N" => UInt256.ofNat

def oldModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := w14 * w13
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 0
  let v5 : W := UInt256.mulMod w10 v4 w9
  let v6 : W := v5 + w1
  let v7 : W := MachineState.readWord s.memory 224
  let v8 : W := UInt256.mulMod w8 v7 w9
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w3 w6 w9
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w7 w5 w9
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w4 w11 w9
  let v15 : W := v14 + v13
  let v16 : W := UInt256.mulMod w13 w14 w9
  let v17 : W := v16 + v15
  let v18 : W := UInt256.land w12 v3
  let v19 : W := v17 - v18
  let v20 : W := w9 + v19
  let v21 : W := UInt256.mulMod v20 (N 2048) w9
  let v22 : W := MachineState.readWord s.memory 64
  let v23 : W := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : W := v23 * v22
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v23 v22 w9
  let v28 : W := v27 + v21
  let v29 : W := MachineState.readWord v24 96
  let v30 : W := MachineState.readWord v24 2016
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v24 128
  let v36 : W := MachineState.readWord v24 1984
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v24 160
  let v42 : W := MachineState.readWord v24 1952
  let v43 : W := v42 * v41
  let v44 : W := v43 + v38
  let v45 : W := UInt256.mulMod v42 v41 w9
  let v46 : W := v45 + v40
  let v47 : W := MachineState.readWord v24 1920
  let v48 : W := v47 * w2
  let v49 : W := v48 + v44
  let v50 : W := UInt256.mulMod v47 w2 w9
  let v51 : W := v50 + v46
  let v52 : W := MachineState.readWord v24 224
  let v53 : W := w10 * v52
  let v54 : W := v53 + v49
  let v55 : W := w8 * w6
  let v56 : W := v55 + v54
  let v57 : W := w3 * w5
  let v58 : W := v57 + v56
  let v59 : W := w7 * w11
  let v60 : W := v59 + v58
  let v61 : W := w4 * w13
  let v62 : W := v61 + v60
  let v63 : W := MachineState.readWord v24 224
  let v64 : W := UInt256.mulMod w10 v63 w9
  let v65 : W := v64 + v51
  let v66 : W := UInt256.mulMod w8 w6 w9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod w3 w5 w9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod w7 w11 w9
  let v71 : W := v70 + v69
  let v72 : W := UInt256.mulMod w4 w13 w9
  let v73 : W := v72 + v71
  let v74 : W := UInt256.land w12 v62
  let v75 : W := v73 - v74
  let v76 : W := w9 + v75
  let v77 : W := UInt256.mulMod v76 (N 2048) w9
  let v78 : W := MachineState.readWord v24 96
  let v79 : W := MachineState.readWord v24 2048
  let v80 : ByteArray := MachineState.writeBytes v24 (Data.Bytes.natToBytesPadded v74.toNat 32) 32
  let v81 : W := v79 * v78
  let v82 : W := v81 + v77
  let v83 : W := UInt256.mulMod v79 v78 w9
  let v84 : W := v83 + v77
  let v85 : W := MachineState.readWord v80 128
  let v86 : W := MachineState.readWord v80 2016
  let v87 : W := v86 * v85
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod v86 v85 w9
  let v90 : W := v89 + v84
  let v91 : W := MachineState.readWord v80 160
  let v92 : W := MachineState.readWord v80 1984
  let v93 : W := v92 * v91
  let v94 : W := v93 + v88
  let v95 : W := UInt256.mulMod v92 v91 w9
  let v96 : W := v95 + v90
  let v97 : W := MachineState.readWord v80 1952
  let v98 : W := v97 * w2
  let v99 : W := v98 + v94
  let v100 : W := UInt256.mulMod v97 w2 w9
  let v101 : W := v100 + v96
  let v102 : W := w10 * w6
  let v103 : W := v102 + v99
  let v104 : W := w8 * w5
  let v105 : W := v104 + v103
  let v106 : W := w3 * w11
  let v107 : W := v106 + v105
  let v108 : W := w7 * w13
  let v109 : W := v108 + v107
  let v110 : W := UInt256.mulMod w10 w6 w9
  let v111 : W := v110 + v101
  let v112 : W := UInt256.mulMod w8 w5 w9
  let v113 : W := v112 + v111
  let v114 : W := UInt256.mulMod w3 w11 w9
  let v115 : W := v114 + v113
  let v116 : W := UInt256.mulMod w7 w13 w9
  let v117 : W := v116 + v115
  let v118 : W := UInt256.land w12 v109
  let v119 : ByteArray := MachineState.writeBytes v80 (Data.Bytes.natToBytesPadded v118.toNat 32) 64
  let v120 : W := v117 - v118
  let v121 : W := w9 + v120
  let v122 : W := UInt256.mulMod v121 (N 2048) w9
  let v123 : W := MachineState.readWord v119 2048
  let v124 : W := MachineState.readWord v119 128
  let v125 : W := MachineState.readWord v119 832
  let v126 : W := v123 * v124
  let v127 : W := v126 + v122
  let v128 : W := UInt256.mulMod v123 v124 w9
  let v129 : W := v128 + v122
  let v130 : W := MachineState.readWord v119 160
  let v131 : W := MachineState.readWord v119 2016
  let v132 : W := v131 * v130
  let v133 : W := v132 + v127
  let v134 : W := UInt256.mulMod v131 v130 w9
  let v135 : W := v134 + v129
  let v136 : W := MachineState.readWord v119 1984
  {s with pc := N 9979, memory := v119, stack := v136 :: w2 :: v133 :: w2 :: w9 :: v135 :: v136 :: w2 :: w3 :: w4 :: w5 :: v125 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

def newpart0Program : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0)]

def newpart0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x5 * x0
  let v1 : W := v0 + x1
  let v2 : W := x15 * x14
  let v3 : W := v2 + v1
  {s with pc := N 9608, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart0Program {s with pc := N 9600, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart0Program, newpart0Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart1Program : List Instr :=
  [.op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD]

def newpart1Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 0
  let v1 : W := UInt256.mulMod x10 v0 x9
  let v2 : W := v1 + x0
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 9618, memory := s.memory, stack := v3 :: x9 :: v2 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart1_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart1Program {s with pc := N 9608, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart1Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha0 : (0 : W).toNat = 0 := rfl
  have hf0 := Monpro.activeWords_fix s 0 32 (by decide) (by norm_num) hact
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart1Program, newpart1Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha0, hf0, ha224, hf224]


def newpart2Program : List Instr :=
  [.op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD]

def newpart2Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x5 x8 x11
  let v3 : W := v2 + v1
  {s with pc := N 9626, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart2_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart2Program {s with pc := N 9618, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart2Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart2Program, newpart2Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart3Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA6)]

def newpart3Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x7 x5 x9
  let v1 : W := v0 + x0
  {s with pc := N 9634, memory := s.memory, stack := x4 :: x11 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart3_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart3Program {s with pc := N 9626, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart3Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart3Program, newpart3Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart4Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0)]

def newpart4Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x16 x17 x12
  let v3 : W := v2 + v1
  {s with pc := N 9642, memory := s.memory, stack := x4 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart4_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart4Program {s with pc := N 9634, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart4Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart4Program, newpart4Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart5Program : List Instr :=
  [.op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD,
   .push 6 2048]

def newpart5Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.land x12 x0
  let v1 : W := x1 - v0
  let v2 : W := x9 + v1
  {s with pc := N 9656, memory := s.memory, stack := (N 2048) :: v2 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart5_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart5Program {s with pc := N 9642, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart5Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 17) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart5Program, newpart5Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart6Program : List Instr :=
  [.op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA9),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA2),
   .push 2 2048,
   .op .MLOAD]

def newpart6Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x10
  let v1 : W := MachineState.readWord s.memory 64
  let v2 : W := MachineState.readWord s.memory 2048
  {s with pc := N 9668, memory := s.memory, stack := v2 :: v0 :: v1 :: x10 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart6_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = N 2048) :
    runInstructions newpart6Program {s with pc := N 9656, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart6Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hk_x0, hz, hzn, newpart6Program, newpart6Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64, ha2048, hf2048]


def newpart7Program : List Instr :=
  [.op (.Swap sA4),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3)]

def newpart7Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x5.toNat 32) 832
  let v1 : W := x0 * x2
  let v2 : W := v1 + x1
  {s with pc := N 9678, memory := v0, stack := x0 :: x2 :: x3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart7_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart7Program {s with pc := N 9668, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart7Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart7Program, newpart7Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832]


def newpart8Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA3)]

def newpart8Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := MachineState.readWord s.memory 96
  let v3 : W := MachineState.readWord s.memory 2016
  {s with pc := N 9689, memory := s.memory, stack := x4 :: v2 :: x12 :: v1 :: v3 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart8_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart8Program {s with pc := N 9678, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart8Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart8Program, newpart8Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha2016, hf2016]


def newpart9Program : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]

def newpart9Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 * x1
  let v1 : W := v0 + x0
  let v2 : W := UInt256.mulMod x4 x1 x2
  let v3 : W := v2 + x3
  {s with pc := N 9697, memory := s.memory, stack := x12 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart9_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart9Program {s with pc := N 9689, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart9Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart9Program, newpart9Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart10Program : List Instr :=
  [.push 1 128,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL]

def newpart10Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 128
  let v1 : W := MachineState.readWord s.memory 1984
  let v2 : W := v1 * v0
  {s with pc := N 9708, memory := s.memory, stack := v2 :: x2 :: v0 :: x0 :: x1 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart10_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart10Program {s with pc := N 9697, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart10Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart10Program, newpart10Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha1984, hf1984]


def newpart11Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 2 160,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD]

def newpart11Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x5 x2 x3
  let v2 : W := v1 + x4
  let v3 : W := MachineState.readWord s.memory 160
  let v4 : W := MachineState.readWord s.memory 1952
  {s with pc := N 9720, memory := s.memory, stack := v4 :: v3 :: v2 :: v0 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart11_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart11Program {s with pc := N 9708, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart11Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart11Program, newpart11Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160, ha1952, hf1952]


def newpart12Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1920,
   .op .MLOAD]

def newpart12Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x1 x0 x11
  let v1 : W := x1 * x0
  let v2 : W := MachineState.readWord s.memory 1920
  {s with pc := N 9730, memory := s.memory, stack := v2 :: v1 :: v0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart12_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart12Program {s with pc := N 9720, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart12Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1920 : (1920 : W).toNat = 1920 := rfl
  have hf1920 := Monpro.activeWords_fix s 1920 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart12Program, newpart12Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1920, hf1920]


def newpart13Program : List Instr :=
  [.op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD]

def newpart13Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := x4 + x1
  let v1 : W := x3 + x2
  let v2 : W := UInt256.mulMod x5 x0 x12
  {s with pc := N 9738, memory := s.memory, stack := v2 :: v1 :: v0 :: x0 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart13_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart13Program {s with pc := N 9730, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart13Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart13Program, newpart13Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart14Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA11)]

def newpart14Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x4 * x3
  let v2 : W := v1 + x2
  let v3 : W := MachineState.readWord s.memory 224
  {s with pc := N 9747, memory := s.memory, stack := x12 :: v3 :: v2 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart14_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart14Program {s with pc := N 9738, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart14Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart14Program, newpart14Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart15Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA4)]

def newpart15Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x10 * x8
  let v3 : W := v2 + v1
  {s with pc := N 9755, memory := s.memory, stack := x5 :: x7 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart15_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart15Program {s with pc := N 9747, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart15Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart15Program, newpart15Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart16Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA5)]

def newpart16Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := x9 * x13
  let v3 : W := v2 + v1
  {s with pc := N 9763, memory := s.memory, stack := x6 :: x15 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart16_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart16Program {s with pc := N 9755, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart16Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart16Program, newpart16Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart17Program : List Instr :=
  [.op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD]

def newpart17Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 * x1
  let v1 : W := v0 + x2
  let v2 : W := MachineState.readWord s.memory 224
  let v3 : W := UInt256.mulMod x12 v2 x11
  {s with pc := N 9772, memory := s.memory, stack := v3 :: x3 :: v1 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart17_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart17Program {s with pc := N 9763, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart17Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha224 : (224 : W).toNat = 224 := rfl
  have hf224 := Monpro.activeWords_fix s 224 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart17Program, newpart17Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha224, hf224]


def newpart18Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6)]

def newpart18Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := UInt256.mulMod x9 x7 x10
  let v2 : W := v1 + v0
  {s with pc := N 9780, memory := s.memory, stack := x6 :: x10 :: v2 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart18_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart18Program {s with pc := N 9772, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart18Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart18Program, newpart18Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart19Program : List Instr :=
  [.op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD]

def newpart19Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := UInt256.mulMod x9 x13 x11
  let v3 : W := v2 + v1
  {s with pc := N 9788, memory := s.memory, stack := v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart19_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart19Program {s with pc := N 9780, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart19Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart19Program, newpart19Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart20Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND]

def newpart20Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x4 x13 x9
  let v1 : W := v0 + x0
  let v2 : W := UInt256.land x12 x1
  {s with pc := N 9796, memory := s.memory, stack := v2 :: v1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart20_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart20Program {s with pc := N 9788, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart20Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart20Program, newpart20Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart21Program : List Instr :=
  [.op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD,
   .push 6 2048,
   .op (.Dup dA10),
   .op (.Swap sA1)]

def newpart21Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := x1 - x0
  let v1 : W := x9 + v0
  {s with pc := N 9810, memory := s.memory, stack := v1 :: (N 2048) :: x9 :: x0 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart21_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart21Program {s with pc := N 9796, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart21Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart21Program, newpart21Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart22Program : List Instr :=
  [.op .MULMOD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA2),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap sA4)]

def newpart22Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord s.memory 96
  let v2 : W := MachineState.readWord s.memory 2048
  {s with pc := N 9821, memory := s.memory, stack := x3 :: v0 :: v1 :: x11 :: v0 :: v2 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart22_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x1 : x1 = N 2048) :
    runInstructions newpart22Program {s with pc := N 9810, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart22Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha96 : (96 : W).toNat = 96 := rfl
  have hf96 := Monpro.activeWords_fix s 96 32 (by decide) (by norm_num) hact
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hk_x1, hz, hzn, newpart22Program, newpart22Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha96, hf96, ha2048, hf2048]


def newpart23Program : List Instr :=
  [.push 1 32,
   .op .MSTORE,
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD]

def newpart23Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 32
  let v1 : W := x5 * x2
  let v2 : W := v1 + x1
  let v3 : W := UInt256.mulMod x5 x2 x3
  {s with pc := N 9830, memory := v0, stack := v3 :: x4 :: v2 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart23_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart23Program {s with pc := N 9821, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart23Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha32 : (32 : W).toNat = 32 := rfl
  have hf32 := Monpro.activeWords_fix s 32 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart23Program, newpart23Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha32, hf32]


def newpart24Program : List Instr :=
  [.op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1)]

def newpart24Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := MachineState.readWord s.memory 2016
  {s with pc := N 9841, memory := s.memory, stack := v1 :: x2 :: v1 :: x10 :: v0 :: v2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart24_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart24Program {s with pc := N 9830, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart24Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart24Program, newpart24Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha2016, hf2016]


def newpart25Program : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 2 160,
   .op .MLOAD]

def newpart25Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W) : State :=
  let v0 : W := x5 * x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.mulMod x5 x2 x3
  let v3 : W := v2 + x4
  let v4 : W := MachineState.readWord s.memory 160
  {s with pc := N 9851, memory := s.memory, stack := v4 :: v3 :: v1 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest}

theorem newpart25_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart25Program {s with pc := N 9841, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: x19 :: rest} =
      some (newpart25Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart25Program, newpart25Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha160, hf160]


def newpart26Program : List Instr :=
  [.push 2 1984,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL]

def newpart26Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1984
  let v1 : W := UInt256.mulMod x0 v0 x10
  let v2 : W := x0 * v0
  {s with pc := N 9861, memory := s.memory, stack := v2 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart26_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart26Program {s with pc := N 9851, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart26Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart26Program, newpart26Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1984, hf1984]


def newpart27Program : List Instr :=
  [.push 2 1952,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3)]

def newpart27Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1952
  let v1 : W := x3 + x0
  let v2 : W := x2 + x1
  {s with pc := N 9871, memory := s.memory, stack := v0 :: x11 :: v2 :: v1 :: v0 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart27_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart27Program {s with pc := N 9861, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart27Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha1952 : (1952 : W).toNat = 1952 := rfl
  have hf1952 := Monpro.activeWords_fix s 1952 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart27Program, newpart27Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1952, hf1952]


def newpart28Program : List Instr :=
  [.op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6)]

def newpart28Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x5 x0 x1
  let v1 : W := v0 + x2
  let v2 : W := x5 * x4
  let v3 : W := v2 + x3
  {s with pc := N 9879, memory := s.memory, stack := x9 :: v3 :: v1 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart28_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart28Program {s with pc := N 9871, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart28Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 20) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart28Program, newpart28Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart29Program : List Instr :=
  [.op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11)]

def newpart29Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x11 * x0
  let v1 : W := v0 + x1
  let v2 : W := x9 * x6
  let v3 : W := v2 + v1
  {s with pc := N 9887, memory := s.memory, stack := x12 :: v3 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart29_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart29Program {s with pc := N 9879, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart29Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart29Program, newpart29Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart30Program : List Instr :=
  [.op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0)]

def newpart30Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := x4 * x0
  let v1 : W := v0 + x1
  let v2 : W := x8 * x14
  let v3 : W := v2 + v1
  {s with pc := N 9895, memory := s.memory, stack := x2 :: v3 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart30_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart30Program {s with pc := N 9887, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart30Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart30Program, newpart30Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart31Program : List Instr :=
  [.op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA10)]

def newpart31Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x10 x6 x9
  let v1 : W := v0 + x0
  {s with pc := N 9903, memory := s.memory, stack := x8 :: x5 :: x9 :: v1 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest}

theorem newpart31_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart31Program {s with pc := N 9895, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: rest} =
      some (newpart31Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart31Program, newpart31Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart32Program : List Instr :=
  [.op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9)]

def newpart32Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := v0 + x3
  let v2 : W := UInt256.mulMod x6 x14 x12
  let v3 : W := v2 + v1
  {s with pc := N 9911, memory := s.memory, stack := x12 :: v3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart32_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart32Program {s with pc := N 9903, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart32Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart32Program, newpart32Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart33Program : List Instr :=
  [.op (.Dup dA14),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0)]

def newpart33Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x8 x14 x0
  let v1 : W := v0 + x1
  let v2 : W := UInt256.land x13 x2
  {s with pc := N 9919, memory := s.memory, stack := v2 :: v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart33_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart33Program {s with pc := N 9911, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart33Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart33Program, newpart33Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart34Program : List Instr :=
  [.push 1 64,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 3 2048]

def newpart34Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded x0.toNat 32) 64
  let v1 : W := x2 - x1
  let v2 : W := x10 + v1
  {s with pc := N 9931, memory := v0, stack := (N 2048) :: v2 :: x10 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart34_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart34Program {s with pc := N 9919, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart34Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha64 : (64 : W).toNat = 64 := rfl
  have hf64 := Monpro.activeWords_fix s 64 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart34Program, newpart34Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha64, hf64]


def newpart35Program : List Instr :=
  [.op .MULMOD,
   .push 1 128,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Dup dA11)]

def newpart35Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x0 x1 x2
  let v1 : W := MachineState.readWord s.memory 128
  let v2 : W := MachineState.readWord s.memory 160
  let v3 : W := MachineState.readWord s.memory 2016
  {s with pc := N 9943, memory := s.memory, stack := x10 :: v3 :: v2 :: v1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart35_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) (hk_x0 : x0 = N 2048) :
    runInstructions newpart35Program {s with pc := N 9931, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart35Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 19) : rest.length + j < 1024 := by omega
  have ha128 : (128 : W).toNat = 128 := rfl
  have hf128 := Monpro.activeWords_fix s 128 32 (by decide) (by norm_num) hact
  have ha160 : (160 : W).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  have ha2016 : (2016 : W).toNat = 2016 := rfl
  have hf2016 := Monpro.activeWords_fix s 2016 32 (by decide) (by norm_num) hact
  simp [hk_x0, hz, hzn, newpart35Program, newpart35Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha128, hf128, ha160, hf160, ha2016, hf2016]


def newpart36Program : List Instr :=
  [.op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA8),
   .op .POP,
   .op .MUL,
   .push 2 2048,
   .op .MLOAD]

def newpart36Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x1 x0
  let v1 : W := x1 * x2
  let v2 : W := MachineState.readWord s.memory 2048
  {s with pc := N 9953, memory := s.memory, stack := v2 :: v1 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: v0 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest}

theorem newpart36_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart36Program {s with pc := N 9943, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: x18 :: rest} =
      some (newpart36Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha2048 : (2048 : W).toNat = 2048 := rfl
  have hf2048 := Monpro.activeWords_fix s 2048 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart36Program, newpart36Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha2048, hf2048]


def newpart37Program : List Instr :=
  [.op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Swap sA2),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD]

def newpart37Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := UInt256.mulMod x2 x0 x11
  let v1 : W := x2 * x0
  let v2 : W := x3 + v1
  {s with pc := N 9961, memory := s.memory, stack := v2 :: x1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart37_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart37Program {s with pc := N 9953, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart37Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  simp [hz, hzn, newpart37Program, newpart37Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity]


def newpart38Program : List Instr :=
  [.op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 832,
   .op .MLOAD,
   .op (.Swap sA6),
   .op .ADD,
   .op (.Dup dA9)]

def newpart38Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W) : State :=
  let v0 : W := x0 + x1
  let v1 : W := x3 + x2
  let v2 : W := MachineState.readWord s.memory 832
  let v3 : W := x8 + v1
  {s with pc := N 9971, memory := s.memory, stack := x11 :: v3 :: v0 :: x4 :: x5 :: x6 :: x7 :: v2 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest}

theorem newpart38_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart38Program {s with pc := N 9961, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: x17 :: rest} =
      some (newpart38Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 18) : rest.length + j < 1024 := by omega
  have ha832 : (832 : W).toNat = 832 := rfl
  have hf832 := Monpro.activeWords_fix s 832 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart38Program, newpart38Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha832, hf832]


def newpart39Program : List Instr :=
  [.op (.Dup dA3),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5)]

def newpart39Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W) : State :=
  let v0 : W := MachineState.readWord s.memory 1984
  {s with pc := N 9979, memory := s.memory, stack := v0 :: x3 :: x2 :: x3 :: x0 :: x1 :: v0 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest}

theorem newpart39_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newpart39Program {s with pc := N 9971, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15 :: x16 :: rest} =
      some (newpart39Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 rest) := by
  have hz : ({val := 0} : W) = N 0 := rfl
  have hzn : ({val := 0} : W).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 21) : rest.length + j < 1024 := by omega
  have ha1984 : (1984 : W).toNat = 1984 := rfl
  have hf1984 := Monpro.activeWords_fix s 1984 32 (by decide) (by norm_num) hact
  simp [hz, hzn, newpart39Program, newpart39Model, runInstructions, runInstr, List.exchange, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, literal_eq_ofNat, capacity, ha1984, hf1984]


def newProgram : List Instr :=
  [.op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA15),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 0 0,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA15),
   .op (.Dup dA15),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD,
   .push 6 2048,
   .op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA9),
   .push 1 64,
   .op .MLOAD,
   .op (.Dup dA2),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap sA4),
   .push 2 832,
   .op .MSTORE,
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 2 160,
   .op .MLOAD,
   .push 2 1952,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1920,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .push 1 224,
   .op .MLOAD,
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA6),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA9),
   .op .ADD,
   .push 6 2048,
   .op (.Dup dA10),
   .op (.Swap sA1),
   .op .MULMOD,
   .op (.Dup dA9),
   .push 1 96,
   .op .MLOAD,
   .op (.Dup dA2),
   .push 2 2048,
   .op .MLOAD,
   .op (.Swap sA4),
   .push 1 32,
   .op .MSTORE,
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .push 1 128,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA3),
   .op .MULMOD,
   .op .ADD,
   .push 2 160,
   .op .MLOAD,
   .push 2 1984,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA1),
   .op .MUL,
   .push 2 1952,
   .op .MLOAD,
   .op (.Swap sA3),
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .op (.Dup dA10),
   .op (.Dup dA3),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA1),
   .op (.Dup dA3),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA6),
   .op (.Dup dA11),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA5),
   .op (.Dup dA9),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA11),
   .op (.Dup dA4),
   .op .MUL,
   .op .ADD,
   .op (.Dup dA13),
   .op (.Dup dA8),
   .op .MUL,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA9),
   .op (.Dup dA7),
   .op (.Dup dA12),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA6),
   .op (.Dup dA10),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA12),
   .op (.Dup dA5),
   .op .MULMOD,
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA14),
   .op (.Dup dA9),
   .op .MULMOD,
   .op .ADD,
   .op (.Swap sA0),
   .op (.Dup dA12),
   .op .AND,
   .op (.Dup dA0),
   .push 1 64,
   .op .MSTORE,
   .op (.Dup dA9),
   .op (.Swap sA1),
   .op .SUB,
   .op (.Dup dA1),
   .op .ADD,
   .push 3 2048,
   .op .MULMOD,
   .push 1 128,
   .op .MLOAD,
   .push 1 160,
   .op .MLOAD,
   .push 2 2016,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA3),
   .op .MULMOD,
   .op (.Swap sA8),
   .op .POP,
   .op .MUL,
   .push 2 2048,
   .op .MLOAD,
   .op (.Dup dA11),
   .op (.Dup dA1),
   .op (.Dup dA4),
   .op .MULMOD,
   .op (.Swap sA2),
   .op .MUL,
   .op (.Dup dA3),
   .op .ADD,
   .op .ADD,
   .op (.Swap sA1),
   .op .ADD,
   .push 2 832,
   .op .MLOAD,
   .op (.Swap sA6),
   .op .ADD,
   .op (.Dup dA9),
   .op (.Dup dA3),
   .push 2 1984,
   .op .MLOAD,
   .op (.Swap sA3),
   .op (.Dup dA1),
   .op (.Dup dA5)]

def newModel (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) : State :=
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := w14 * w13
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 0
  let v5 : W := UInt256.mulMod w10 v4 w9
  let v6 : W := v5 + w1
  let v7 : W := MachineState.readWord s.memory 224
  let v8 : W := UInt256.mulMod w8 v7 w9
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w3 w6 w9
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w7 w5 w9
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w4 w11 w9
  let v15 : W := v14 + v13
  let v16 : W := UInt256.mulMod w13 w14 w9
  let v17 : W := v16 + v15
  let v18 : W := UInt256.land w12 v3
  let v19 : W := v17 - v18
  let v20 : W := w9 + v19
  let v21 : W := UInt256.mulMod v20 (N 2048) w9
  let v22 : W := MachineState.readWord s.memory 64
  let v23 : W := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : W := v23 * v22
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v23 v22 w9
  let v28 : W := v27 + v21
  let v29 : W := MachineState.readWord v24 96
  let v30 : W := MachineState.readWord v24 2016
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v24 128
  let v36 : W := MachineState.readWord v24 1984
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v24 160
  let v42 : W := MachineState.readWord v24 1952
  let v43 : W := UInt256.mulMod v41 v42 w9
  let v44 : W := v41 * v42
  let v45 : W := MachineState.readWord v24 1920
  let v46 : W := v38 + v44
  let v47 : W := v40 + v43
  let v48 : W := UInt256.mulMod w2 v45 w9
  let v49 : W := v48 + v47
  let v50 : W := w2 * v45
  let v51 : W := v50 + v46
  let v52 : W := MachineState.readWord v24 224
  let v53 : W := w10 * v52
  let v54 : W := v53 + v51
  let v55 : W := w8 * w6
  let v56 : W := v55 + v54
  let v57 : W := w3 * w5
  let v58 : W := v57 + v56
  let v59 : W := w7 * w11
  let v60 : W := v59 + v58
  let v61 : W := w4 * w13
  let v62 : W := v61 + v60
  let v63 : W := MachineState.readWord v24 224
  let v64 : W := UInt256.mulMod w10 v63 w9
  let v65 : W := v64 + v49
  let v66 : W := UInt256.mulMod w8 w6 w9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod w3 w5 w9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod w7 w11 w9
  let v71 : W := v70 + v69
  let v72 : W := UInt256.mulMod w4 w13 w9
  let v73 : W := v72 + v71
  let v74 : W := UInt256.land w12 v62
  let v75 : W := v73 - v74
  let v76 : W := w9 + v75
  let v77 : W := UInt256.mulMod v76 (N 2048) w9
  let v78 : W := MachineState.readWord v24 96
  let v79 : W := MachineState.readWord v24 2048
  let v80 : ByteArray := MachineState.writeBytes v24 (Data.Bytes.natToBytesPadded v74.toNat 32) 32
  let v81 : W := v79 * v78
  let v82 : W := v81 + v77
  let v83 : W := UInt256.mulMod v79 v78 w9
  let v84 : W := v83 + v77
  let v85 : W := MachineState.readWord v80 128
  let v86 : W := MachineState.readWord v80 2016
  let v87 : W := v86 * v85
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod v86 v85 w9
  let v90 : W := v89 + v84
  let v91 : W := MachineState.readWord v80 160
  let v92 : W := MachineState.readWord v80 1984
  let v93 : W := UInt256.mulMod v91 v92 w9
  let v94 : W := v91 * v92
  let v95 : W := MachineState.readWord v80 1952
  let v96 : W := v88 + v94
  let v97 : W := v90 + v93
  let v98 : W := UInt256.mulMod w2 v95 w9
  let v99 : W := v98 + v97
  let v100 : W := w2 * v95
  let v101 : W := v100 + v96
  let v102 : W := w10 * w6
  let v103 : W := v102 + v101
  let v104 : W := w8 * w5
  let v105 : W := v104 + v103
  let v106 : W := w3 * w11
  let v107 : W := v106 + v105
  let v108 : W := w7 * w13
  let v109 : W := v108 + v107
  let v110 : W := UInt256.mulMod w10 w6 w9
  let v111 : W := v110 + v99
  let v112 : W := UInt256.mulMod w8 w5 w9
  let v113 : W := v112 + v111
  let v114 : W := UInt256.mulMod w3 w11 w9
  let v115 : W := v114 + v113
  let v116 : W := UInt256.mulMod w7 w13 w9
  let v117 : W := v116 + v115
  let v118 : W := UInt256.land w12 v109
  let v119 : ByteArray := MachineState.writeBytes v80 (Data.Bytes.natToBytesPadded v118.toNat 32) 64
  let v120 : W := v117 - v118
  let v121 : W := w9 + v120
  let v122 : W := UInt256.mulMod (N 2048) v121 w9
  let v123 : W := MachineState.readWord v119 128
  let v124 : W := MachineState.readWord v119 160
  let v125 : W := MachineState.readWord v119 2016
  let v126 : W := UInt256.mulMod v124 v125 w9
  let v127 : W := v125 * v124
  let v128 : W := MachineState.readWord v119 2048
  let v129 : W := UInt256.mulMod v123 v128 w9
  let v130 : W := v123 * v128
  let v131 : W := v122 + v130
  let v132 : W := v131 + v127
  let v133 : W := v122 + v129
  let v134 : W := MachineState.readWord v119 832
  let v135 : W := v126 + v133
  let v136 : W := MachineState.readWord v119 1984
  {s with pc := N 9979, memory := v119, stack := v136 :: w2 :: v132 :: w2 :: w9 :: v135 :: v136 :: w2 :: w3 :: w4 :: w5 :: v134 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}

theorem new_run (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions newProgram {s with pc := N 9600, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
      some (newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest) := by
  let v0 : W := w4 * carry
  let v1 : W := v0 + w0
  let v2 : W := w14 * w13
  let v3 : W := v2 + v1
  let v4 : W := MachineState.readWord s.memory 0
  let v5 : W := UInt256.mulMod w10 v4 w9
  let v6 : W := v5 + w1
  let v7 : W := MachineState.readWord s.memory 224
  let v8 : W := UInt256.mulMod w8 v7 w9
  let v9 : W := v8 + v6
  let v10 : W := UInt256.mulMod w3 w6 w9
  let v11 : W := v10 + v9
  let v12 : W := UInt256.mulMod w7 w5 w9
  let v13 : W := v12 + v11
  let v14 : W := UInt256.mulMod w4 w11 w9
  let v15 : W := v14 + v13
  let v16 : W := UInt256.mulMod w13 w14 w9
  let v17 : W := v16 + v15
  let v18 : W := UInt256.land w12 v3
  let v19 : W := v17 - v18
  let v20 : W := w9 + v19
  let v21 : W := UInt256.mulMod v20 (N 2048) w9
  let v22 : W := MachineState.readWord s.memory 64
  let v23 : W := MachineState.readWord s.memory 2048
  let v24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v18.toNat 32) 832
  let v25 : W := v23 * v22
  let v26 : W := v25 + v21
  let v27 : W := UInt256.mulMod v23 v22 w9
  let v28 : W := v27 + v21
  let v29 : W := MachineState.readWord v24 96
  let v30 : W := MachineState.readWord v24 2016
  let v31 : W := v30 * v29
  let v32 : W := v31 + v26
  let v33 : W := UInt256.mulMod v30 v29 w9
  let v34 : W := v33 + v28
  let v35 : W := MachineState.readWord v24 128
  let v36 : W := MachineState.readWord v24 1984
  let v37 : W := v36 * v35
  let v38 : W := v37 + v32
  let v39 : W := UInt256.mulMod v36 v35 w9
  let v40 : W := v39 + v34
  let v41 : W := MachineState.readWord v24 160
  let v42 : W := MachineState.readWord v24 1952
  let v43 : W := UInt256.mulMod v41 v42 w9
  let v44 : W := v41 * v42
  let v45 : W := MachineState.readWord v24 1920
  let v46 : W := v38 + v44
  let v47 : W := v40 + v43
  let v48 : W := UInt256.mulMod w2 v45 w9
  let v49 : W := v48 + v47
  let v50 : W := w2 * v45
  let v51 : W := v50 + v46
  let v52 : W := MachineState.readWord v24 224
  let v53 : W := w10 * v52
  let v54 : W := v53 + v51
  let v55 : W := w8 * w6
  let v56 : W := v55 + v54
  let v57 : W := w3 * w5
  let v58 : W := v57 + v56
  let v59 : W := w7 * w11
  let v60 : W := v59 + v58
  let v61 : W := w4 * w13
  let v62 : W := v61 + v60
  let v63 : W := MachineState.readWord v24 224
  let v64 : W := UInt256.mulMod w10 v63 w9
  let v65 : W := v64 + v49
  let v66 : W := UInt256.mulMod w8 w6 w9
  let v67 : W := v66 + v65
  let v68 : W := UInt256.mulMod w3 w5 w9
  let v69 : W := v68 + v67
  let v70 : W := UInt256.mulMod w7 w11 w9
  let v71 : W := v70 + v69
  let v72 : W := UInt256.mulMod w4 w13 w9
  let v73 : W := v72 + v71
  let v74 : W := UInt256.land w12 v62
  let v75 : W := v73 - v74
  let v76 : W := w9 + v75
  let v77 : W := UInt256.mulMod v76 (N 2048) w9
  let v78 : W := MachineState.readWord v24 96
  let v79 : W := MachineState.readWord v24 2048
  let v80 : ByteArray := MachineState.writeBytes v24 (Data.Bytes.natToBytesPadded v74.toNat 32) 32
  let v81 : W := v79 * v78
  let v82 : W := v81 + v77
  let v83 : W := UInt256.mulMod v79 v78 w9
  let v84 : W := v83 + v77
  let v85 : W := MachineState.readWord v80 128
  let v86 : W := MachineState.readWord v80 2016
  let v87 : W := v86 * v85
  let v88 : W := v87 + v82
  let v89 : W := UInt256.mulMod v86 v85 w9
  let v90 : W := v89 + v84
  let v91 : W := MachineState.readWord v80 160
  let v92 : W := MachineState.readWord v80 1984
  let v93 : W := UInt256.mulMod v91 v92 w9
  let v94 : W := v91 * v92
  let v95 : W := MachineState.readWord v80 1952
  let v96 : W := v88 + v94
  let v97 : W := v90 + v93
  let v98 : W := UInt256.mulMod w2 v95 w9
  let v99 : W := v98 + v97
  let v100 : W := w2 * v95
  let v101 : W := v100 + v96
  let v102 : W := w10 * w6
  let v103 : W := v102 + v101
  let v104 : W := w8 * w5
  let v105 : W := v104 + v103
  let v106 : W := w3 * w11
  let v107 : W := v106 + v105
  let v108 : W := w7 * w13
  let v109 : W := v108 + v107
  let v110 : W := UInt256.mulMod w10 w6 w9
  let v111 : W := v110 + v99
  let v112 : W := UInt256.mulMod w8 w5 w9
  let v113 : W := v112 + v111
  let v114 : W := UInt256.mulMod w3 w11 w9
  let v115 : W := v114 + v113
  let v116 : W := UInt256.mulMod w7 w13 w9
  let v117 : W := v116 + v115
  let v118 : W := UInt256.land w12 v109
  let v119 : ByteArray := MachineState.writeBytes v80 (Data.Bytes.natToBytesPadded v118.toNat 32) 64
  let v120 : W := v117 - v118
  let v121 : W := w9 + v120
  let v122 : W := UInt256.mulMod (N 2048) v121 w9
  let v123 : W := MachineState.readWord v119 128
  let v124 : W := MachineState.readWord v119 160
  let v125 : W := MachineState.readWord v119 2016
  let v126 : W := UInt256.mulMod v124 v125 w9
  let v127 : W := v125 * v124
  let v128 : W := MachineState.readWord v119 2048
  let v129 : W := UInt256.mulMod v123 v128 w9
  let v130 : W := v123 * v128
  let v131 : W := v122 + v130
  let v132 : W := v131 + v127
  let v133 : W := v122 + v129
  let v134 : W := MachineState.readWord v119 832
  let v135 : W := v126 + v133
  let v136 : W := MachineState.readWord v119 1984
  have h0 : runInstructions newpart0Program {s with pc := N 9600, memory := s.memory, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9608, memory := s.memory, stack := w1 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart0Model, v0, v1, v2, v3] using newpart0_run (s) (carry) (w0) (w1) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h1 : runInstructions newpart1Program {s with pc := N 9608, memory := s.memory, stack := w1 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9618, memory := s.memory, stack := v7 :: w9 :: v6 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart1Model, v4, v5, v6, v7] using newpart1_run (s) (w1) (v3) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h2 : runInstructions newpart2Program {s with pc := N 9618, memory := s.memory, stack := v7 :: w9 :: v6 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9626, memory := s.memory, stack := v11 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart2Model, v8, v9, v10, v11] using newpart2_run (s) (v7) (w9) (v6) (v3) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h3 : runInstructions newpart3Program {s with pc := N 9626, memory := s.memory, stack := v11 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9634, memory := s.memory, stack := w4 :: w11 :: w9 :: v13 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart3Model, v12, v13] using newpart3_run (s) (v11) (v3) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h4 : runInstructions newpart4Program {s with pc := N 9634, memory := s.memory, stack := w4 :: w11 :: w9 :: v13 :: v3 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9642, memory := s.memory, stack := v3 :: v17 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart4Model, v14, v15, v16, v17] using newpart4_run (s) (w4) (w11) (w9) (v13) (v3) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h5 : runInstructions newpart5Program {s with pc := N 9642, memory := s.memory, stack := v3 :: v17 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9656, memory := s.memory, stack := (N 2048) :: v20 :: v18 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart5Model, v18, v19, v20] using newpart5_run (s) (v3) (v17) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h6 : runInstructions newpart6Program {s with pc := N 9656, memory := s.memory, stack := (N 2048) :: v20 :: v18 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9668, memory := s.memory, stack := v23 :: v21 :: v22 :: w9 :: v21 :: v18 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart6Model, v21, v22, v23] using newpart6_run (s) ((N 2048)) (v20) (v18) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact (by rfl)
  have h7 : runInstructions newpart7Program {s with pc := N 9668, memory := s.memory, stack := v23 :: v21 :: v22 :: w9 :: v21 :: v18 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9678, memory := v24, stack := v23 :: v22 :: w9 :: v21 :: v26 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart7Model, v24, v25, v26] using newpart7_run (s) (v23) (v21) (v22) (w9) (v21) (v18) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h8 : runInstructions newpart8Program {s with pc := N 9678, memory := v24, stack := v23 :: v22 :: w9 :: v21 :: v26 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9689, memory := v24, stack := v26 :: v29 :: w9 :: v28 :: v30 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart8Model, v27, v28, v29, v30] using newpart8_run ({s with memory := v24}) (v23) (v22) (w9) (v21) (v26) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h9 : runInstructions newpart9Program {s with pc := N 9689, memory := v24, stack := v26 :: v29 :: w9 :: v28 :: v30 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9697, memory := v24, stack := w9 :: v34 :: v32 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart9Model, v31, v32, v33, v34] using newpart9_run ({s with memory := v24}) (v26) (v29) (w9) (v28) (v30) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h10 : runInstructions newpart10Program {s with pc := N 9697, memory := v24, stack := w9 :: v34 :: v32 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9708, memory := v24, stack := v37 :: v32 :: v35 :: w9 :: v34 :: v36 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart10Model, v35, v36, v37] using newpart10_run ({s with memory := v24}) (w9) (v34) (v32) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h11 : runInstructions newpart11Program {s with pc := N 9708, memory := v24, stack := v37 :: v32 :: v35 :: w9 :: v34 :: v36 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9720, memory := v24, stack := v42 :: v41 :: v40 :: v38 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart11Model, v38, v39, v40, v41, v42] using newpart11_run ({s with memory := v24}) (v37) (v32) (v35) (w9) (v34) (v36) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h12 : runInstructions newpart12Program {s with pc := N 9720, memory := v24, stack := v42 :: v41 :: v40 :: v38 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9730, memory := v24, stack := v45 :: v44 :: v43 :: v40 :: v38 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart12Model, v43, v44, v45] using newpart12_run ({s with memory := v24}) (v42) (v41) (v40) (v38) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h13 : runInstructions newpart13Program {s with pc := N 9730, memory := v24, stack := v45 :: v44 :: v43 :: v40 :: v38 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9738, memory := v24, stack := v48 :: v47 :: v46 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart13Model, v46, v47, v48] using newpart13_run ({s with memory := v24}) (v45) (v44) (v43) (v40) (v38) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h14 : runInstructions newpart14Program {s with pc := N 9738, memory := v24, stack := v48 :: v47 :: v46 :: v45 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9747, memory := v24, stack := w10 :: v52 :: v51 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart14Model, v49, v50, v51, v52] using newpart14_run ({s with memory := v24}) (v48) (v47) (v46) (v45) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h15 : runInstructions newpart15Program {s with pc := N 9747, memory := v24, stack := w10 :: v52 :: v51 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9755, memory := v24, stack := w3 :: w5 :: v56 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart15Model, v53, v54, v55, v56] using newpart15_run ({s with memory := v24}) (w10) (v52) (v51) (v49) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h16 : runInstructions newpart16Program {s with pc := N 9755, memory := v24, stack := w3 :: w5 :: v56 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9763, memory := v24, stack := w4 :: w13 :: v60 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart16Model, v57, v58, v59, v60] using newpart16_run ({s with memory := v24}) (w3) (w5) (v56) (v49) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h17 : runInstructions newpart17Program {s with pc := N 9763, memory := v24, stack := w4 :: w13 :: v60 :: v49 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9772, memory := v24, stack := v64 :: v49 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart17Model, v61, v62, v63, v64] using newpart17_run ({s with memory := v24}) (w4) (w13) (v60) (v49) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h18 : runInstructions newpart18Program {s with pc := N 9772, memory := v24, stack := v64 :: v49 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9780, memory := v24, stack := w5 :: w9 :: v67 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart18Model, v65, v66, v67] using newpart18_run ({s with memory := v24}) (v64) (v49) (v62) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h19 : runInstructions newpart19Program {s with pc := N 9780, memory := v24, stack := w5 :: w9 :: v67 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9788, memory := v24, stack := v71 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart19Model, v68, v69, v70, v71] using newpart19_run ({s with memory := v24}) (w5) (w9) (v67) (v62) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h20 : runInstructions newpart20Program {s with pc := N 9788, memory := v24, stack := v71 :: v62 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9796, memory := v24, stack := v74 :: v73 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart20Model, v72, v73, v74] using newpart20_run ({s with memory := v24}) (v71) (v62) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h21 : runInstructions newpart21Program {s with pc := N 9796, memory := v24, stack := v74 :: v73 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9810, memory := v24, stack := v76 :: (N 2048) :: w9 :: v74 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart21Model, v75, v76] using newpart21_run ({s with memory := v24}) (v74) (v73) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h22 : runInstructions newpart22Program {s with pc := N 9810, memory := v24, stack := v76 :: (N 2048) :: w9 :: v74 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9821, memory := v24, stack := v74 :: v77 :: v78 :: w9 :: v77 :: v79 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart22Model, v77, v78, v79] using newpart22_run ({s with memory := v24}) (v76) ((N 2048)) (w9) (v74) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact (by rfl)
  have h23 : runInstructions newpart23Program {s with pc := N 9821, memory := v24, stack := v74 :: v77 :: v78 :: w9 :: v77 :: v79 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9830, memory := v80, stack := v83 :: v77 :: v82 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart23Model, v80, v81, v82, v83] using newpart23_run ({s with memory := v24}) (v74) (v77) (v78) (w9) (v77) (v79) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h24 : runInstructions newpart24Program {s with pc := N 9830, memory := v80, stack := v83 :: v77 :: v82 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9841, memory := v80, stack := v85 :: v82 :: v85 :: w9 :: v84 :: v86 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart24Model, v84, v85, v86] using newpart24_run ({s with memory := v80}) (v83) (v77) (v82) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h25 : runInstructions newpart25Program {s with pc := N 9841, memory := v80, stack := v85 :: v82 :: v85 :: w9 :: v84 :: v86 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9851, memory := v80, stack := v91 :: v90 :: v88 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart25Model, v87, v88, v89, v90, v91] using newpart25_run ({s with memory := v80}) (v85) (v82) (v85) (w9) (v84) (v86) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h26 : runInstructions newpart26Program {s with pc := N 9851, memory := v80, stack := v91 :: v90 :: v88 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9861, memory := v80, stack := v94 :: v93 :: v90 :: v88 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart26Model, v92, v93, v94] using newpart26_run ({s with memory := v80}) (v91) (v90) (v88) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h27 : runInstructions newpart27Program {s with pc := N 9861, memory := v80, stack := v94 :: v93 :: v90 :: v88 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9871, memory := v80, stack := v95 :: w9 :: v97 :: v96 :: v95 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart27Model, v95, v96, v97] using newpart27_run ({s with memory := v80}) (v94) (v93) (v90) (v88) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h28 : runInstructions newpart28Program {s with pc := N 9871, memory := v80, stack := v95 :: w9 :: v97 :: v96 :: v95 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9879, memory := v80, stack := w6 :: v101 :: v99 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart28Model, v98, v99, v100, v101] using newpart28_run ({s with memory := v80}) (v95) (w9) (v97) (v96) (v95) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h29 : runInstructions newpart29Program {s with pc := N 9879, memory := v80, stack := w6 :: v101 :: v99 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9887, memory := v80, stack := w11 :: v105 :: v99 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart29Model, v102, v103, v104, v105] using newpart29_run ({s with memory := v80}) (w6) (v101) (v99) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h30 : runInstructions newpart30Program {s with pc := N 9887, memory := v80, stack := w11 :: v105 :: v99 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9895, memory := v80, stack := v99 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart30Model, v106, v107, v108, v109] using newpart30_run ({s with memory := v80}) (w11) (v105) (v99) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h31 : runInstructions newpart31Program {s with pc := N 9895, memory := v80, stack := v99 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9903, memory := v80, stack := w8 :: w5 :: w9 :: v111 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart31Model, v110, v111] using newpart31_run ({s with memory := v80}) (v99) (v109) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h32 : runInstructions newpart32Program {s with pc := N 9903, memory := v80, stack := w8 :: w5 :: w9 :: v111 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9911, memory := v80, stack := w9 :: v115 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart32Model, v112, v113, v114, v115] using newpart32_run ({s with memory := v80}) (w8) (w5) (w9) (v111) (v109) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h33 : runInstructions newpart33Program {s with pc := N 9911, memory := v80, stack := w9 :: v115 :: v109 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9919, memory := v80, stack := v118 :: v118 :: v117 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart33Model, v116, v117, v118] using newpart33_run ({s with memory := v80}) (w9) (v115) (v109) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h34 : runInstructions newpart34Program {s with pc := N 9919, memory := v80, stack := v118 :: v118 :: v117 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9931, memory := v119, stack := (N 2048) :: v121 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart34Model, v119, v120, v121] using newpart34_run ({s with memory := v80}) (v118) (v118) (v117) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h35 : runInstructions newpart35Program {s with pc := N 9931, memory := v119, stack := (N 2048) :: v121 :: w9 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9943, memory := v119, stack := w9 :: v125 :: v124 :: v123 :: v122 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart35Model, v122, v123, v124, v125] using newpart35_run ({s with memory := v119}) ((N 2048)) (v121) (w9) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact (by rfl)
  have h36 : runInstructions newpart36Program {s with pc := N 9943, memory := v119, stack := w9 :: v125 :: v124 :: v123 :: v122 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9953, memory := v119, stack := v128 :: v127 :: v123 :: v122 :: w2 :: w3 :: w4 :: w5 :: v126 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart36Model, v126, v127, v128] using newpart36_run ({s with memory := v119}) (w9) (v125) (v124) (v123) (v122) (w2) (w3) (w4) (w5) (w6) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h37 : runInstructions newpart37Program {s with pc := N 9953, memory := v119, stack := v128 :: v127 :: v123 :: v122 :: w2 :: w3 :: w4 :: w5 :: v126 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9961, memory := v119, stack := v131 :: v127 :: v129 :: v122 :: w2 :: w3 :: w4 :: w5 :: v126 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart37Model, v129, v130, v131] using newpart37_run ({s with memory := v119}) (v128) (v127) (v123) (v122) (w2) (w3) (w4) (w5) (v126) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h38 : runInstructions newpart38Program {s with pc := N 9961, memory := v119, stack := v131 :: v127 :: v129 :: v122 :: w2 :: w3 :: w4 :: w5 :: v126 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9971, memory := v119, stack := w9 :: v135 :: v132 :: w2 :: w3 :: w4 :: w5 :: v134 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart38Model, v132, v133, v134, v135] using newpart38_run ({s with memory := v119}) (v131) (v127) (v129) (v122) (w2) (w3) (w4) (w5) (v126) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  have h39 : runInstructions newpart39Program {s with pc := N 9971, memory := v119, stack := w9 :: v135 :: v132 :: w2 :: w3 :: w4 :: w5 :: v134 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} = some {s with pc := N 9979, memory := v119, stack := v136 :: w2 :: v132 :: w2 :: w9 :: v135 :: v136 :: w2 :: w3 :: w4 :: w5 :: v134 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} := by
    simpa only [newpart39Model, v136] using newpart39_run ({s with memory := v119}) (w9) (v135) (v132) (w2) (w3) (w4) (w5) (v134) (w7) (w8) (w9) (w10) (w11) (w12) (w13) (w14) (w15) rest hcap hact
  exact (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 (runInstructions_append_some _ _ _ _ _ h17 (runInstructions_append_some _ _ _ _ _ h18 (runInstructions_append_some _ _ _ _ _ h19 (runInstructions_append_some _ _ _ _ _ h20 (runInstructions_append_some _ _ _ _ _ h21 (runInstructions_append_some _ _ _ _ _ h22 (runInstructions_append_some _ _ _ _ _ h23 (runInstructions_append_some _ _ _ _ _ h24 (runInstructions_append_some _ _ _ _ _ h25 (runInstructions_append_some _ _ _ _ _ h26 (runInstructions_append_some _ _ _ _ _ h27 (runInstructions_append_some _ _ _ _ _ h28 (runInstructions_append_some _ _ _ _ _ h29 (runInstructions_append_some _ _ _ _ _ h30 (runInstructions_append_some _ _ _ _ _ h31 (runInstructions_append_some _ _ _ _ _ h32 (runInstructions_append_some _ _ _ _ _ h33 (runInstructions_append_some _ _ _ _ _ h34 (runInstructions_append_some _ _ _ _ _ h35 (runInstructions_append_some _ _ _ _ _ h36 (runInstructions_append_some _ _ _ _ _ h37 (runInstructions_append_some _ _ _ _ _ h38 h39)))))))))))))))))))))))))))))))))))))))

#print axioms new_run

private theorem aux_shared0 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 832) 224) = (MachineState.readWord s.memory 224) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared1 (s : State) (z0 : W) :
    (MachineState.readWord (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 832) 2048) = (MachineState.readWord s.memory 2048) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared2 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) 128) = (MachineState.readWord z0 128) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared3 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) 2016) = (MachineState.readWord z0 2016) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared4 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) 160) = (MachineState.readWord z0 160) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared5 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) 1984) = (MachineState.readWord z0 1984) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared6 (z1 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) 1952) = (MachineState.readWord z0 1952) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared7 (s : State) (z0 z1 z2 : W) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded z0.toNat 32) 832) (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 2048) = (MachineState.readWord s.memory 2048) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared8 (z1 z2 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 128) = (MachineState.readWord z0 128) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared9 (s : State) (w12 : W) (z0 z1 z2 : W) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (UInt256.land w12 z0).toNat 32) 832) (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 832) = (UInt256.land w12 z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared10 (z1 z2 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 160) = (MachineState.readWord z0 160) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared11 (z1 z2 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 2016) = (MachineState.readWord z0 2016) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared12 (z1 z2 : W) (z0 : ByteArray) :
    (MachineState.readWord (MachineState.writeBytes (MachineState.writeBytes z0 (Data.Bytes.natToBytesPadded z1.toNat 32) 32) (Data.Bytes.natToBytesPadded z2.toNat 32) 64) 1984) = (MachineState.readWord z0 1984) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared13 (w9 : W) (z0 z1 : W) :
    (UInt256.mulMod z0 z1 w9) = (UInt256.mulMod z1 z0 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared14 (z0 z1 : W) :
    (z0 * z1) = (z1 * z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared15 (z0 z1 : W) :
    (z0 + z1) = (z1 + z0) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared16 (w2 w9 : W) (z0 : W) :
    (UInt256.mulMod w2 z0 w9) = (UInt256.mulMod z0 w2 w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared17 (w2 : W) (z0 : W) :
    (w2 * z0) = (z0 * w2) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

private theorem aux_shared18 (w9 : W) (z0 : W) :
    (UInt256.mulMod (N 2048) z0 w9) = (UInt256.mulMod z0 (N 2048) w9) := by
  simp (disch := decide) only [addC, addA, addL, mulC, mmC, amC, andC, orC, xorC, eqC, read_disjoint, Challenge.EvmProof.Memory.readWord_writeWord]

theorem same_state (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = newModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest := by
  let o0 : W := w4 * carry
  let o1 : W := o0 + w0
  let o2 : W := w14 * w13
  let o3 : W := o2 + o1
  let o4 : W := MachineState.readWord s.memory 0
  let o5 : W := UInt256.mulMod w10 o4 w9
  let o6 : W := o5 + w1
  let o7 : W := MachineState.readWord s.memory 224
  let o8 : W := UInt256.mulMod w8 o7 w9
  let o9 : W := o8 + o6
  let o10 : W := UInt256.mulMod w3 w6 w9
  let o11 : W := o10 + o9
  let o12 : W := UInt256.mulMod w7 w5 w9
  let o13 : W := o12 + o11
  let o14 : W := UInt256.mulMod w4 w11 w9
  let o15 : W := o14 + o13
  let o16 : W := UInt256.mulMod w13 w14 w9
  let o17 : W := o16 + o15
  let o18 : W := UInt256.land w12 o3
  let o19 : W := o17 - o18
  let o20 : W := w9 + o19
  let o21 : W := UInt256.mulMod o20 (N 2048) w9
  let o22 : W := MachineState.readWord s.memory 64
  let o23 : W := MachineState.readWord s.memory 2048
  let o24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded o18.toNat 32) 832
  let o25 : W := o23 * o22
  let o26 : W := o25 + o21
  let o27 : W := UInt256.mulMod o23 o22 w9
  let o28 : W := o27 + o21
  let o29 : W := MachineState.readWord o24 96
  let o30 : W := MachineState.readWord o24 2016
  let o31 : W := o30 * o29
  let o32 : W := o31 + o26
  let o33 : W := UInt256.mulMod o30 o29 w9
  let o34 : W := o33 + o28
  let o35 : W := MachineState.readWord o24 128
  let o36 : W := MachineState.readWord o24 1984
  let o37 : W := o36 * o35
  let o38 : W := o37 + o32
  let o39 : W := UInt256.mulMod o36 o35 w9
  let o40 : W := o39 + o34
  let o41 : W := MachineState.readWord o24 160
  let o42 : W := MachineState.readWord o24 1952
  let o43 : W := o42 * o41
  let o44 : W := o43 + o38
  let o45 : W := UInt256.mulMod o42 o41 w9
  let o46 : W := o45 + o40
  let o47 : W := MachineState.readWord o24 1920
  let o48 : W := o47 * w2
  let o49 : W := o48 + o44
  let o50 : W := UInt256.mulMod o47 w2 w9
  let o51 : W := o50 + o46
  let o52 : W := MachineState.readWord o24 224
  let o53 : W := w10 * o52
  let o54 : W := o53 + o49
  let o55 : W := w8 * w6
  let o56 : W := o55 + o54
  let o57 : W := w3 * w5
  let o58 : W := o57 + o56
  let o59 : W := w7 * w11
  let o60 : W := o59 + o58
  let o61 : W := w4 * w13
  let o62 : W := o61 + o60
  let o63 : W := MachineState.readWord o24 224
  let o64 : W := UInt256.mulMod w10 o63 w9
  let o65 : W := o64 + o51
  let o66 : W := UInt256.mulMod w8 w6 w9
  let o67 : W := o66 + o65
  let o68 : W := UInt256.mulMod w3 w5 w9
  let o69 : W := o68 + o67
  let o70 : W := UInt256.mulMod w7 w11 w9
  let o71 : W := o70 + o69
  let o72 : W := UInt256.mulMod w4 w13 w9
  let o73 : W := o72 + o71
  let o74 : W := UInt256.land w12 o62
  let o75 : W := o73 - o74
  let o76 : W := w9 + o75
  let o77 : W := UInt256.mulMod o76 (N 2048) w9
  let o78 : W := MachineState.readWord o24 96
  let o79 : W := MachineState.readWord o24 2048
  let o80 : ByteArray := MachineState.writeBytes o24 (Data.Bytes.natToBytesPadded o74.toNat 32) 32
  let o81 : W := o79 * o78
  let o82 : W := o81 + o77
  let o83 : W := UInt256.mulMod o79 o78 w9
  let o84 : W := o83 + o77
  let o85 : W := MachineState.readWord o80 128
  let o86 : W := MachineState.readWord o80 2016
  let o87 : W := o86 * o85
  let o88 : W := o87 + o82
  let o89 : W := UInt256.mulMod o86 o85 w9
  let o90 : W := o89 + o84
  let o91 : W := MachineState.readWord o80 160
  let o92 : W := MachineState.readWord o80 1984
  let o93 : W := o92 * o91
  let o94 : W := o93 + o88
  let o95 : W := UInt256.mulMod o92 o91 w9
  let o96 : W := o95 + o90
  let o97 : W := MachineState.readWord o80 1952
  let o98 : W := o97 * w2
  let o99 : W := o98 + o94
  let o100 : W := UInt256.mulMod o97 w2 w9
  let o101 : W := o100 + o96
  let o102 : W := w10 * w6
  let o103 : W := o102 + o99
  let o104 : W := w8 * w5
  let o105 : W := o104 + o103
  let o106 : W := w3 * w11
  let o107 : W := o106 + o105
  let o108 : W := w7 * w13
  let o109 : W := o108 + o107
  let o110 : W := UInt256.mulMod w10 w6 w9
  let o111 : W := o110 + o101
  let o112 : W := UInt256.mulMod w8 w5 w9
  let o113 : W := o112 + o111
  let o114 : W := UInt256.mulMod w3 w11 w9
  let o115 : W := o114 + o113
  let o116 : W := UInt256.mulMod w7 w13 w9
  let o117 : W := o116 + o115
  let o118 : W := UInt256.land w12 o109
  let o119 : ByteArray := MachineState.writeBytes o80 (Data.Bytes.natToBytesPadded o118.toNat 32) 64
  let o120 : W := o117 - o118
  let o121 : W := w9 + o120
  let o122 : W := UInt256.mulMod o121 (N 2048) w9
  let o123 : W := MachineState.readWord o119 2048
  let o124 : W := MachineState.readWord o119 128
  let o125 : W := MachineState.readWord o119 832
  let o126 : W := o123 * o124
  let o127 : W := o126 + o122
  let o128 : W := UInt256.mulMod o123 o124 w9
  let o129 : W := o128 + o122
  let o130 : W := MachineState.readWord o119 160
  let o131 : W := MachineState.readWord o119 2016
  let o132 : W := o131 * o130
  let o133 : W := o132 + o127
  let o134 : W := UInt256.mulMod o131 o130 w9
  let o135 : W := o134 + o129
  let o136 : W := MachineState.readWord o119 1984
  let n0 : W := w4 * carry
  let n1 : W := n0 + w0
  let n2 : W := w14 * w13
  let n3 : W := n2 + n1
  let n4 : W := MachineState.readWord s.memory 0
  let n5 : W := UInt256.mulMod w10 n4 w9
  let n6 : W := n5 + w1
  let n7 : W := MachineState.readWord s.memory 224
  let n8 : W := UInt256.mulMod w8 n7 w9
  let n9 : W := n8 + n6
  let n10 : W := UInt256.mulMod w3 w6 w9
  let n11 : W := n10 + n9
  let n12 : W := UInt256.mulMod w7 w5 w9
  let n13 : W := n12 + n11
  let n14 : W := UInt256.mulMod w4 w11 w9
  let n15 : W := n14 + n13
  let n16 : W := UInt256.mulMod w13 w14 w9
  let n17 : W := n16 + n15
  let n18 : W := UInt256.land w12 n3
  let n19 : W := n17 - n18
  let n20 : W := w9 + n19
  let n21 : W := UInt256.mulMod n20 (N 2048) w9
  let n22 : W := MachineState.readWord s.memory 64
  let n23 : W := MachineState.readWord s.memory 2048
  let n24 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded n18.toNat 32) 832
  let n25 : W := n23 * n22
  let n26 : W := n25 + n21
  let n27 : W := UInt256.mulMod n23 n22 w9
  let n28 : W := n27 + n21
  let n29 : W := MachineState.readWord n24 96
  let n30 : W := MachineState.readWord n24 2016
  let n31 : W := n30 * n29
  let n32 : W := n31 + n26
  let n33 : W := UInt256.mulMod n30 n29 w9
  let n34 : W := n33 + n28
  let n35 : W := MachineState.readWord n24 128
  let n36 : W := MachineState.readWord n24 1984
  let n37 : W := n36 * n35
  let n38 : W := n37 + n32
  let n39 : W := UInt256.mulMod n36 n35 w9
  let n40 : W := n39 + n34
  let n41 : W := MachineState.readWord n24 160
  let n42 : W := MachineState.readWord n24 1952
  let n43 : W := UInt256.mulMod n41 n42 w9
  let n44 : W := n41 * n42
  let n45 : W := MachineState.readWord n24 1920
  let n46 : W := n38 + n44
  let n47 : W := n40 + n43
  let n48 : W := UInt256.mulMod w2 n45 w9
  let n49 : W := n48 + n47
  let n50 : W := w2 * n45
  let n51 : W := n50 + n46
  let n52 : W := MachineState.readWord n24 224
  let n53 : W := w10 * n52
  let n54 : W := n53 + n51
  let n55 : W := w8 * w6
  let n56 : W := n55 + n54
  let n57 : W := w3 * w5
  let n58 : W := n57 + n56
  let n59 : W := w7 * w11
  let n60 : W := n59 + n58
  let n61 : W := w4 * w13
  let n62 : W := n61 + n60
  let n63 : W := MachineState.readWord n24 224
  let n64 : W := UInt256.mulMod w10 n63 w9
  let n65 : W := n64 + n49
  let n66 : W := UInt256.mulMod w8 w6 w9
  let n67 : W := n66 + n65
  let n68 : W := UInt256.mulMod w3 w5 w9
  let n69 : W := n68 + n67
  let n70 : W := UInt256.mulMod w7 w11 w9
  let n71 : W := n70 + n69
  let n72 : W := UInt256.mulMod w4 w13 w9
  let n73 : W := n72 + n71
  let n74 : W := UInt256.land w12 n62
  let n75 : W := n73 - n74
  let n76 : W := w9 + n75
  let n77 : W := UInt256.mulMod n76 (N 2048) w9
  let n78 : W := MachineState.readWord n24 96
  let n79 : W := MachineState.readWord n24 2048
  let n80 : ByteArray := MachineState.writeBytes n24 (Data.Bytes.natToBytesPadded n74.toNat 32) 32
  let n81 : W := n79 * n78
  let n82 : W := n81 + n77
  let n83 : W := UInt256.mulMod n79 n78 w9
  let n84 : W := n83 + n77
  let n85 : W := MachineState.readWord n80 128
  let n86 : W := MachineState.readWord n80 2016
  let n87 : W := n86 * n85
  let n88 : W := n87 + n82
  let n89 : W := UInt256.mulMod n86 n85 w9
  let n90 : W := n89 + n84
  let n91 : W := MachineState.readWord n80 160
  let n92 : W := MachineState.readWord n80 1984
  let n93 : W := UInt256.mulMod n91 n92 w9
  let n94 : W := n91 * n92
  let n95 : W := MachineState.readWord n80 1952
  let n96 : W := n88 + n94
  let n97 : W := n90 + n93
  let n98 : W := UInt256.mulMod w2 n95 w9
  let n99 : W := n98 + n97
  let n100 : W := w2 * n95
  let n101 : W := n100 + n96
  let n102 : W := w10 * w6
  let n103 : W := n102 + n101
  let n104 : W := w8 * w5
  let n105 : W := n104 + n103
  let n106 : W := w3 * w11
  let n107 : W := n106 + n105
  let n108 : W := w7 * w13
  let n109 : W := n108 + n107
  let n110 : W := UInt256.mulMod w10 w6 w9
  let n111 : W := n110 + n99
  let n112 : W := UInt256.mulMod w8 w5 w9
  let n113 : W := n112 + n111
  let n114 : W := UInt256.mulMod w3 w11 w9
  let n115 : W := n114 + n113
  let n116 : W := UInt256.mulMod w7 w13 w9
  let n117 : W := n116 + n115
  let n118 : W := UInt256.land w12 n109
  let n119 : ByteArray := MachineState.writeBytes n80 (Data.Bytes.natToBytesPadded n118.toNat 32) 64
  let n120 : W := n117 - n118
  let n121 : W := w9 + n120
  let n122 : W := UInt256.mulMod (N 2048) n121 w9
  let n123 : W := MachineState.readWord n119 128
  let n124 : W := MachineState.readWord n119 160
  let n125 : W := MachineState.readWord n119 2016
  let n126 : W := UInt256.mulMod n124 n125 w9
  let n127 : W := n125 * n124
  let n128 : W := MachineState.readWord n119 2048
  let n129 : W := UInt256.mulMod n123 n128 w9
  let n130 : W := n123 * n128
  let n131 : W := n122 + n130
  let n132 : W := n131 + n127
  let n133 : W := n122 + n129
  let n134 : W := MachineState.readWord n119 832
  let n135 : W := n126 + n133
  let n136 : W := MachineState.readWord n119 1984
  have eq_o52 : o52 = o7 := by
    simpa only [o52, o24, o7] using
      (aux_shared0 s  o18)
  have eq_o63 : o63 = o7 := by
    simpa only [o63, o24, o7] using
      (aux_shared0 s  o18)
  have eq_o78 : o78 = o29 := by
    simp only [o78, o29]
  have eq_o79 : o79 = o23 := by
    simpa only [o79, o24, o23] using
      (aux_shared1 s  o18)
  have eq_o85 : o85 = o35 := by
    simpa only [o85, o80, o35] using
      (aux_shared2  o74 o24)
  have eq_o86 : o86 = o30 := by
    simpa only [o86, o80, o30] using
      (aux_shared3  o74 o24)
  have eq_o91 : o91 = o41 := by
    simpa only [o91, o80, o41] using
      (aux_shared4  o74 o24)
  have eq_o92 : o92 = o36 := by
    simpa only [o92, o80, o36] using
      (aux_shared5  o74 o24)
  have eq_o97 : o97 = o42 := by
    simpa only [o97, o80, o42] using
      (aux_shared6  o74 o24)
  have eq_o123 : o123 = o23 := by
    simpa only [o123, o119, o80, o24, o23] using
      (aux_shared7 s  o18 o74 o118)
  have eq_o124 : o124 = o35 := by
    simpa only [o124, o119, o80, o35] using
      (aux_shared8  o74 o118 o24)
  have eq_o125 : o125 = o18 := by
    simpa only [o125, o119, o80, o24, o18] using
      (aux_shared9 s w12 o3 o74 o118)
  have eq_o130 : o130 = o41 := by
    simpa only [o130, o119, o80, o41] using
      (aux_shared10  o74 o118 o24)
  have eq_o131 : o131 = o30 := by
    simpa only [o131, o119, o80, o30] using
      (aux_shared11  o74 o118 o24)
  have eq_o136 : o136 = o36 := by
    simpa only [o136, o119, o80, o36] using
      (aux_shared12  o74 o118 o24)
  have eq_n0 : n0 = o0 := by
    simp only [n0, o0]
  have eq_n1 : n1 = o1 := by
    simp only [n1, o1, eq_n0]
  have eq_n2 : n2 = o2 := by
    simp only [n2, o2]
  have eq_n3 : n3 = o3 := by
    simp only [n3, o3, eq_n2, eq_n1]
  have eq_n4 : n4 = o4 := by
    simp only [n4, o4]
  have eq_n5 : n5 = o5 := by
    simp only [n5, o5, eq_n4]
  have eq_n6 : n6 = o6 := by
    simp only [n6, o6, eq_n5]
  have eq_n7 : n7 = o7 := by
    simp only [n7, o7]
  have eq_n8 : n8 = o8 := by
    simp only [n8, o8, eq_n7]
  have eq_n9 : n9 = o9 := by
    simp only [n9, o9, eq_n8, eq_n6]
  have eq_n10 : n10 = o10 := by
    simp only [n10, o10]
  have eq_n11 : n11 = o11 := by
    simp only [n11, o11, eq_n10, eq_n9]
  have eq_n12 : n12 = o12 := by
    simp only [n12, o12]
  have eq_n13 : n13 = o13 := by
    simp only [n13, o13, eq_n12, eq_n11]
  have eq_n14 : n14 = o14 := by
    simp only [n14, o14]
  have eq_n15 : n15 = o15 := by
    simp only [n15, o15, eq_n14, eq_n13]
  have eq_n16 : n16 = o16 := by
    simp only [n16, o16]
  have eq_n17 : n17 = o17 := by
    simp only [n17, o17, eq_n16, eq_n15]
  have eq_n18 : n18 = o18 := by
    simp only [n18, o18, eq_n3]
  have eq_n19 : n19 = o19 := by
    simp only [n19, o19, eq_n17, eq_n18]
  have eq_n20 : n20 = o20 := by
    simp only [n20, o20, eq_n19]
  have eq_n21 : n21 = o21 := by
    simp only [n21, o21, eq_n20]
  have eq_n22 : n22 = o22 := by
    simp only [n22, o22]
  have eq_n23 : n23 = o23 := by
    simp only [n23, o23]
  have eq_n24 : n24 = o24 := by
    simp only [n24, o24, eq_n18]
  have eq_n25 : n25 = o25 := by
    simp only [n25, o25, eq_n23, eq_n22]
  have eq_n26 : n26 = o26 := by
    simp only [n26, o26, eq_n25, eq_n21]
  have eq_n27 : n27 = o27 := by
    simp only [n27, o27, eq_n23, eq_n22]
  have eq_n28 : n28 = o28 := by
    simp only [n28, o28, eq_n27, eq_n21]
  have eq_n29 : n29 = o29 := by
    simp only [n29, o29, eq_n24]
  have eq_n30 : n30 = o30 := by
    simp only [n30, o30, eq_n24]
  have eq_n31 : n31 = o31 := by
    simp only [n31, o31, eq_n30, eq_n29]
  have eq_n32 : n32 = o32 := by
    simp only [n32, o32, eq_n31, eq_n26]
  have eq_n33 : n33 = o33 := by
    simp only [n33, o33, eq_n30, eq_n29]
  have eq_n34 : n34 = o34 := by
    simp only [n34, o34, eq_n33, eq_n28]
  have eq_n35 : n35 = o35 := by
    simp only [n35, o35, eq_n24]
  have eq_n36 : n36 = o36 := by
    simp only [n36, o36, eq_n24]
  have eq_n37 : n37 = o37 := by
    simp only [n37, o37, eq_n36, eq_n35]
  have eq_n38 : n38 = o38 := by
    simp only [n38, o38, eq_n37, eq_n32]
  have eq_n39 : n39 = o39 := by
    simp only [n39, o39, eq_n36, eq_n35]
  have eq_n40 : n40 = o40 := by
    simp only [n40, o40, eq_n39, eq_n34]
  have eq_n41 : n41 = o41 := by
    simp only [n41, o41, eq_n24]
  have eq_n42 : n42 = o42 := by
    simp only [n42, o42, eq_n24]
  have eq_n43 : n43 = o45 := by
    simpa only [n43, o45, eq_n41, eq_n42] using
      (aux_shared13 w9 o41 o42)
  have eq_n44 : n44 = o43 := by
    simpa only [n44, o43, eq_n41, eq_n42] using
      (aux_shared14  o41 o42)
  have eq_n45 : n45 = o47 := by
    simp only [n45, o47, eq_n24]
  have eq_n46 : n46 = o44 := by
    simpa only [n46, o44, eq_n38, eq_n44] using
      (aux_shared15  o38 o43)
  have eq_n47 : n47 = o46 := by
    simpa only [n47, o46, eq_n40, eq_n43] using
      (aux_shared15  o40 o45)
  have eq_n48 : n48 = o50 := by
    simpa only [n48, o50, eq_n45] using
      (aux_shared16 w2 w9 o47)
  have eq_n49 : n49 = o51 := by
    simp only [n49, o51, eq_n48, eq_n47]
  have eq_n50 : n50 = o48 := by
    simpa only [n50, o48, eq_n45] using
      (aux_shared17 w2 o47)
  have eq_n51 : n51 = o49 := by
    simp only [n51, o49, eq_n50, eq_n46]
  have eq_n52 : n52 = o7 := by
    simpa only [n52, n24, o7, eq_n18] using
      (aux_shared0 s  o18)
  have eq_n53 : n53 = o53 := by
    simp only [n53, o53, eq_n52, eq_o52]
  have eq_n54 : n54 = o54 := by
    simp only [n54, o54, eq_n53, eq_n51]
  have eq_n55 : n55 = o55 := by
    simp only [n55, o55]
  have eq_n56 : n56 = o56 := by
    simp only [n56, o56, eq_n55, eq_n54]
  have eq_n57 : n57 = o57 := by
    simp only [n57, o57]
  have eq_n58 : n58 = o58 := by
    simp only [n58, o58, eq_n57, eq_n56]
  have eq_n59 : n59 = o59 := by
    simp only [n59, o59]
  have eq_n60 : n60 = o60 := by
    simp only [n60, o60, eq_n59, eq_n58]
  have eq_n61 : n61 = o61 := by
    simp only [n61, o61]
  have eq_n62 : n62 = o62 := by
    simp only [n62, o62, eq_n61, eq_n60]
  have eq_n63 : n63 = o7 := by
    simpa only [n63, n24, o7, eq_n18] using
      (aux_shared0 s  o18)
  have eq_n64 : n64 = o64 := by
    simp only [n64, o64, eq_n63, eq_o63]
  have eq_n65 : n65 = o65 := by
    simp only [n65, o65, eq_n64, eq_n49]
  have eq_n66 : n66 = o66 := by
    simp only [n66, o66]
  have eq_n67 : n67 = o67 := by
    simp only [n67, o67, eq_n66, eq_n65]
  have eq_n68 : n68 = o68 := by
    simp only [n68, o68]
  have eq_n69 : n69 = o69 := by
    simp only [n69, o69, eq_n68, eq_n67]
  have eq_n70 : n70 = o70 := by
    simp only [n70, o70]
  have eq_n71 : n71 = o71 := by
    simp only [n71, o71, eq_n70, eq_n69]
  have eq_n72 : n72 = o72 := by
    simp only [n72, o72]
  have eq_n73 : n73 = o73 := by
    simp only [n73, o73, eq_n72, eq_n71]
  have eq_n74 : n74 = o74 := by
    simp only [n74, o74, eq_n62]
  have eq_n75 : n75 = o75 := by
    simp only [n75, o75, eq_n73, eq_n74]
  have eq_n76 : n76 = o76 := by
    simp only [n76, o76, eq_n75]
  have eq_n77 : n77 = o77 := by
    simp only [n77, o77, eq_n76]
  have eq_n78 : n78 = o29 := by
    simp only [n78, o29, eq_n24]
  have eq_n79 : n79 = o23 := by
    simpa only [n79, n24, o23, eq_n18] using
      (aux_shared1 s  o18)
  have eq_n80 : n80 = o80 := by
    simp only [n80, o80, eq_n24, eq_n74]
  have eq_n81 : n81 = o81 := by
    simp only [n81, o81, eq_n79, eq_n78, eq_o79, eq_o78]
  have eq_n82 : n82 = o82 := by
    simp only [n82, o82, eq_n81, eq_n77]
  have eq_n83 : n83 = o83 := by
    simp only [n83, o83, eq_n79, eq_n78, eq_o79, eq_o78]
  have eq_n84 : n84 = o84 := by
    simp only [n84, o84, eq_n83, eq_n77]
  have eq_n85 : n85 = o35 := by
    simpa only [n85, n80, o35, eq_n24, eq_n74] using
      (aux_shared2  o74 o24)
  have eq_n86 : n86 = o30 := by
    simpa only [n86, n80, o30, eq_n24, eq_n74] using
      (aux_shared3  o74 o24)
  have eq_n87 : n87 = o87 := by
    simp only [n87, o87, eq_n86, eq_n85, eq_o86, eq_o85]
  have eq_n88 : n88 = o88 := by
    simp only [n88, o88, eq_n87, eq_n82]
  have eq_n89 : n89 = o89 := by
    simp only [n89, o89, eq_n86, eq_n85, eq_o86, eq_o85]
  have eq_n90 : n90 = o90 := by
    simp only [n90, o90, eq_n89, eq_n84]
  have eq_n91 : n91 = o41 := by
    simpa only [n91, n80, o41, eq_n24, eq_n74] using
      (aux_shared4  o74 o24)
  have eq_n92 : n92 = o36 := by
    simpa only [n92, n80, o36, eq_n24, eq_n74] using
      (aux_shared5  o74 o24)
  have eq_n93 : n93 = o95 := by
    simpa only [n93, o95, eq_n91, eq_n92, eq_o92, eq_o91] using
      (aux_shared13 w9 o41 o36)
  have eq_n94 : n94 = o93 := by
    simpa only [n94, o93, eq_n91, eq_n92, eq_o92, eq_o91] using
      (aux_shared14  o41 o36)
  have eq_n95 : n95 = o42 := by
    simpa only [n95, n80, o42, eq_n24, eq_n74] using
      (aux_shared6  o74 o24)
  have eq_n96 : n96 = o94 := by
    simpa only [n96, o94, eq_n88, eq_n94] using
      (aux_shared15  o88 o93)
  have eq_n97 : n97 = o96 := by
    simpa only [n97, o96, eq_n90, eq_n93] using
      (aux_shared15  o90 o95)
  have eq_n98 : n98 = o100 := by
    simpa only [n98, o100, eq_n95, eq_o97] using
      (aux_shared16 w2 w9 o42)
  have eq_n99 : n99 = o101 := by
    simp only [n99, o101, eq_n98, eq_n97]
  have eq_n100 : n100 = o98 := by
    simpa only [n100, o98, eq_n95, eq_o97] using
      (aux_shared17 w2 o42)
  have eq_n101 : n101 = o99 := by
    simp only [n101, o99, eq_n100, eq_n96]
  have eq_n102 : n102 = o102 := by
    simp only [n102, o102]
  have eq_n103 : n103 = o103 := by
    simp only [n103, o103, eq_n102, eq_n101]
  have eq_n104 : n104 = o104 := by
    simp only [n104, o104]
  have eq_n105 : n105 = o105 := by
    simp only [n105, o105, eq_n104, eq_n103]
  have eq_n106 : n106 = o106 := by
    simp only [n106, o106]
  have eq_n107 : n107 = o107 := by
    simp only [n107, o107, eq_n106, eq_n105]
  have eq_n108 : n108 = o108 := by
    simp only [n108, o108]
  have eq_n109 : n109 = o109 := by
    simp only [n109, o109, eq_n108, eq_n107]
  have eq_n110 : n110 = o110 := by
    simp only [n110, o110]
  have eq_n111 : n111 = o111 := by
    simp only [n111, o111, eq_n110, eq_n99]
  have eq_n112 : n112 = o112 := by
    simp only [n112, o112]
  have eq_n113 : n113 = o113 := by
    simp only [n113, o113, eq_n112, eq_n111]
  have eq_n114 : n114 = o114 := by
    simp only [n114, o114]
  have eq_n115 : n115 = o115 := by
    simp only [n115, o115, eq_n114, eq_n113]
  have eq_n116 : n116 = o116 := by
    simp only [n116, o116]
  have eq_n117 : n117 = o117 := by
    simp only [n117, o117, eq_n116, eq_n115]
  have eq_n118 : n118 = o118 := by
    simp only [n118, o118, eq_n109]
  have eq_n119 : n119 = o119 := by
    simp only [n119, o119, eq_n80, eq_n118]
  have eq_n120 : n120 = o120 := by
    simp only [n120, o120, eq_n117, eq_n118]
  have eq_n121 : n121 = o121 := by
    simp only [n121, o121, eq_n120]
  have eq_n122 : n122 = o122 := by
    simpa only [n122, o122, eq_n121] using
      (aux_shared18 w9 o121)
  have eq_n123 : n123 = o35 := by
    simpa only [n123, n119, n80, o35, eq_n24, eq_n74, eq_n118] using
      (aux_shared8  o74 o118 o24)
  have eq_n124 : n124 = o41 := by
    simpa only [n124, n119, n80, o41, eq_n24, eq_n74, eq_n118] using
      (aux_shared10  o74 o118 o24)
  have eq_n125 : n125 = o30 := by
    simpa only [n125, n119, n80, o30, eq_n24, eq_n74, eq_n118] using
      (aux_shared11  o74 o118 o24)
  have eq_n126 : n126 = o134 := by
    simpa only [n126, o134, eq_n124, eq_n125, eq_o131, eq_o130] using
      (aux_shared13 w9 o41 o30)
  have eq_n127 : n127 = o132 := by
    simp only [n127, o132, eq_n125, eq_n124, eq_o131, eq_o130]
  have eq_n128 : n128 = o23 := by
    simpa only [n128, n119, n80, n24, o23, eq_n18, eq_n74, eq_n118] using
      (aux_shared7 s  o18 o74 o118)
  have eq_n129 : n129 = o128 := by
    simpa only [n129, o128, eq_n123, eq_n128, eq_o123, eq_o124] using
      (aux_shared13 w9 o35 o23)
  have eq_n130 : n130 = o126 := by
    simpa only [n130, o126, eq_n123, eq_n128, eq_o123, eq_o124] using
      (aux_shared14  o35 o23)
  have eq_n131 : n131 = o127 := by
    simpa only [n131, o127, eq_n122, eq_n130] using
      (aux_shared15  o122 o126)
  have eq_n132 : n132 = o133 := by
    simpa only [n132, o133, eq_n131, eq_n127] using
      (aux_shared15  o127 o132)
  have eq_n133 : n133 = o129 := by
    simpa only [n133, o129, eq_n122, eq_n129] using
      (aux_shared15  o122 o128)
  have eq_n134 : n134 = o18 := by
    simpa only [n134, n119, n80, n24, n18, o18, eq_n3, eq_n74, eq_n118] using
      (aux_shared9 s w12 o3 o74 o118)
  have eq_n135 : n135 = o135 := by
    simp only [n135, o135, eq_n126, eq_n133]
  have eq_n136 : n136 = o36 := by
    simpa only [n136, n119, n80, o36, eq_n24, eq_n74, eq_n118] using
      (aux_shared12  o74 o118 o24)
  change {s with pc := N 9979, memory := o119, stack := o136 :: w2 :: o133 :: w2 :: w9 :: o135 :: o136 :: w2 :: w3 :: w4 :: w5 :: o125 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest} =
    {s with pc := N 9979, memory := n119, stack := n136 :: w2 :: n132 :: w2 :: w9 :: n135 :: n136 :: w2 :: w3 :: w4 :: w5 :: n134 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}
  simp only [eq_o52, eq_o63, eq_o78, eq_o79, eq_o85, eq_o86, eq_o91, eq_o92, eq_o97, eq_o123, eq_o124, eq_o125, eq_o130, eq_o131, eq_o136, eq_n0, eq_n1, eq_n2, eq_n3, eq_n4, eq_n5, eq_n6, eq_n7, eq_n8, eq_n9, eq_n10, eq_n11, eq_n12, eq_n13, eq_n14, eq_n15, eq_n16, eq_n17, eq_n18, eq_n19, eq_n20, eq_n21, eq_n22, eq_n23, eq_n24, eq_n25, eq_n26, eq_n27, eq_n28, eq_n29, eq_n30, eq_n31, eq_n32, eq_n33, eq_n34, eq_n35, eq_n36, eq_n37, eq_n38, eq_n39, eq_n40, eq_n41, eq_n42, eq_n43, eq_n44, eq_n45, eq_n46, eq_n47, eq_n48, eq_n49, eq_n50, eq_n51, eq_n52, eq_n53, eq_n54, eq_n55, eq_n56, eq_n57, eq_n58, eq_n59, eq_n60, eq_n61, eq_n62, eq_n63, eq_n64, eq_n65, eq_n66, eq_n67, eq_n68, eq_n69, eq_n70, eq_n71, eq_n72, eq_n73, eq_n74, eq_n75, eq_n76, eq_n77, eq_n78, eq_n79, eq_n80, eq_n81, eq_n82, eq_n83, eq_n84, eq_n85, eq_n86, eq_n87, eq_n88, eq_n89, eq_n90, eq_n91, eq_n92, eq_n93, eq_n94, eq_n95, eq_n96, eq_n97, eq_n98, eq_n99, eq_n100, eq_n101, eq_n102, eq_n103, eq_n104, eq_n105, eq_n106, eq_n107, eq_n108, eq_n109, eq_n110, eq_n111, eq_n112, eq_n113, eq_n114, eq_n115, eq_n116, eq_n117, eq_n118, eq_n119, eq_n120, eq_n121, eq_n122, eq_n123, eq_n124, eq_n125, eq_n126, eq_n127, eq_n128, eq_n129, eq_n130, eq_n131, eq_n132, eq_n133, eq_n134, eq_n135, eq_n136]

def eval15 (s : State) : State :=
  productColumn15Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack.drop 17)

def eval16 (s : State) : State :=
  productColumn16Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack.drop 16)

def eval17 (s : State) : State :=
  productColumn17Model s (s.stack[0]!) (s.stack[1]!) (s.stack[2]!) (s.stack[3]!) (s.stack[4]!) (s.stack[5]!) (s.stack[6]!) (s.stack[7]!) (s.stack[8]!) (s.stack[9]!) (s.stack[10]!) (s.stack[11]!) (s.stack[12]!) (s.stack[13]!) (s.stack[14]!) (s.stack[15]!) (s.stack[16]!) (s.stack[17]!) (s.stack[18]!) (s.stack.drop 19)

theorem old_eval (s : State) (carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : W) (rest : List W) :
    oldModel s carry w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 rest = eval17 (eval16 (eval15 ({s with pc := N 9600, stack := carry :: w0 :: w1 :: w2 :: w3 :: w4 :: w5 :: w6 :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 :: w14 :: w15 :: rest}))) := by
  rfl

#print axioms old_eval
#print axioms new_run
#print axioms same_state
end CycleSubmission.Prepared.ProductGroup9668

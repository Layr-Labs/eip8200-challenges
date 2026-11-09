import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square0
import Challenge.Modexp.Submission.Proofs.Cycle.Meaning.Square1
import Challenge.Modexp.Submission.Proofs.Cycle.DoubleInput01

set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000

/-! The exact fused columns 0+1 return the historical frame at PC 5968.
There is deliberately no equality claim about the transient frame at PC 5840. -/
namespace CycleSubmission.SquareMeaning
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.EvmProof.Word

private theorem mul_comm01 (x y : UInt256) : x*y = y*x := by
  apply word_ext
  change (x.val * y.val).val = (y.val * x.val).val
  rw [mul_comm]

/-- The fused model retains the historical result, including both memory writes. -/
theorem model01_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256)
    (rest : List UInt256) (h : Memory0 s.memory inv a b n)
    (ha0 : (a 0).toNat < radix) :
    DoubleInput01.mergedModel s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7)
      P (n 8) (n 1) (UInt256.ofNat (2^240-1)) (n 0) (n 3) (a 8) rest =
        result1 (result0 s inv a b n rest) inv a b n rest := by
  let v0 : UInt256 := MachineState.readWord (s.memory) 768
  have eq0 : v0 = a 0 := by
    simp (disch := decide) only [v0, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v1 : UInt256 := v0 * v0
  let v2 : UInt256 := MachineState.readWord (s.memory) 2720
  have eq2 : v2 = inv := by
    simp (disch := decide) only [v2, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v3 : UInt256 := v2 * v1
  let v4 : UInt256 := UInt256.land (UInt256.ofNat (2^240-1)) v3
  have eq4 : v4 = squareQ0 inv a b n := by
    simp (disch := decide) only [v1, v3, v4, eq0, eq2, squareQ0, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v5 : UInt256 := UInt256.mulMod v0 v0 P
  let v6 : UInt256 := UInt256.mulMod (n 0) v4 P
  let v7 : UInt256 := v6 + v5
  let v8 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v7 P
  have eq8 : v8 = squareC1 inv a b n := by
    simp (disch := decide) only [v5, v6, v7, v8, eq0, eq4, squareC1, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v9 : UInt256 := MachineState.readWord (s.memory) 768
  have eq9 : v9 = a 0 := by
    simp (disch := decide) only [v9, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v10 : UInt256 := v9 + v9
  let v11 : UInt256 := UInt256.mulMod (a 1) v10 P
  let v12 : UInt256 := (a 1) * v10
  have eq12 : v12 = a 1 * a 0 + a 1 * a 0 := by
    simp (disch := decide) only [v10, v12, eq9, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v13 : UInt256 := v8 + v12
  let v14 : UInt256 := (n 1) * v4
  let v15 : UInt256 := v14 + v13
  let v16 : UInt256 := v8 + v11
  let v17 : UInt256 := UInt256.mulMod v4 (n 1) P
  let v18 : UInt256 := v17 + v16
  let v19 : UInt256 := MachineState.readWord (s.memory) 2720
  have eq19 : v19 = inv := by
    simp (disch := decide) only [v19, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v20 : UInt256 := v15 * v19
  let v21 : UInt256 := UInt256.land (UInt256.ofNat (2^240-1)) v20
  have eq21 : v21 = squareQ1 inv a b n := by
    simp (disch := decide) only [v13, v14, v15, v20, v21, eq4, eq8, eq12, eq19, squareQ1, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
    simp only [DoubleInput.addA, word_add_comm, DoubleInput.addL, mul_comm01]
  let v22 : UInt256 := UInt256.mulMod v21 (n 0) P
  let v23 : UInt256 := v22 + v18
  let v24 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v23 P
  have eq24 : v24 = squareC2 inv a b n := by
    have hh := DoubleInput.high_double_radix240 (a 0) (a 1) (UInt256.ofNat 2048)
      (UInt256.mulMod (n 0) (squareQ0 inv a b n) P + UInt256.mulMod (a 0) (a 0) P)
      (squareQ0 inv a b n) (n 1) (squareQ1 inv a b n) (n 0)
      (UInt256.ofNat 2048) ha0
    change UInt256.mulMod (UInt256.ofNat 2048)
      (UInt256.mulMod (squareQ1 inv a b n) (n 0) P +
        (UInt256.mulMod (squareQ0 inv a b n) (n 1) P +
          (squareC1 inv a b n + UInt256.mulMod (a 1) (a 0 + a 0) P))) P = _ at hh
    simpa only [v10, v11, v16, v17, v18, v22, v23, v24, eq4, eq8, eq9, eq21, squareC2, squareC1, P, HistoricalSearch.CRTColumn.residueModulus] using hh
  let v25 : UInt256 := MachineState.readWord (s.memory) 768
  have eq25 : v25 = a 0 := by
    simp (disch := decide) only [v25, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v26 : UInt256 := v4 * (n 2)
  let v27 : UInt256 := (a 1) * (a 1)
  let v28 : UInt256 := UInt256.mulMod (a 2) v25 P
  let v29 : UInt256 := v28 + v28
  let v30 : UInt256 := (a 2) * v25
  let v31 : UInt256 := v30 + v30
  let v32 : UInt256 := v24 + v31
  let v33 : UInt256 := v32 + v27
  let v34 : UInt256 := v33 + v26
  let v35 : UInt256 := (n 1) * v21
  let v36 : UInt256 := v35 + v34
  let v37 : UInt256 := v24 + v29
  let v38 : UInt256 := UInt256.mulMod (a 1) (a 1) P
  let v39 : UInt256 := v38 + v37
  let v40 : UInt256 := UInt256.mulMod v4 (n 2) P
  let v41 : UInt256 := v40 + v39
  let v42 : UInt256 := UInt256.mulMod v21 (n 1) P
  let v43 : UInt256 := v42 + v41
  let v44 : UInt256 := MachineState.readWord (s.memory) 2720
  have eq44 : v44 = inv := by
    simp (disch := decide) only [v44, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v45 : UInt256 := v36 * v44
  let v46 : UInt256 := UInt256.land (UInt256.ofNat (2^240-1)) v45
  have eq46 : v46 = squareQ2 inv a b n := by
    simp (disch := decide) only [v26, v27, v30, v31, v32, v33, v34, v35, v36, v45, v46, eq4, eq21, eq24, eq25, eq44, squareQ2, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
    simp only [DoubleInput.addA, word_add_comm, DoubleInput.addL, mul_comm01]
  let v47 : ByteArray := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded v46.toNat 32) 192
  have eq47 : v47 = MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (squareQ2 inv a b n).toNat 32) 192 := by
    simp (disch := decide) only [v47, eq46, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v48 : UInt256 := UInt256.mulMod v46 (n 0) P
  let v49 : UInt256 := v48 + v43
  let v50 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v49 P
  have eq50 : v50 = squareC3 inv a b n := by
    simp (disch := decide) only [v28, v29, v37, v38, v39, v40, v41, v42, v43, v48, v49, v50, eq4, eq21, eq24, eq25, eq46, squareC3, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v51 : UInt256 := MachineState.readWord (v47) 32
  have eq51 : v51 = a 3 := by
    simp (disch := decide) only [v51, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v52 : UInt256 := MachineState.readWord (v47) 768
  have eq52 : v52 = a 0 := by
    simp (disch := decide) only [v52, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v53 : UInt256 := v51 * v52
  let v54 : UInt256 := (a 1) * (a 2)
  let v55 : UInt256 := v54 + v53
  let v56 : UInt256 := v55 + v55
  let v57 : UInt256 := UInt256.mulMod v51 v52 P
  let v58 : UInt256 := UInt256.mulMod (a 1) (a 2) P
  let v59 : UInt256 := v58 + v57
  let v60 : UInt256 := v59 + v59
  let v61 : UInt256 := v50 + v60
  let v62 : UInt256 := v50 + v56
  let v63 : UInt256 := v4 * (n 3)
  let v64 : UInt256 := v63 + v62
  let v65 : UInt256 := v21 * (n 2)
  let v66 : UInt256 := v65 + v64
  let v67 : UInt256 := MachineState.readWord (v47) 192
  have eq67 : v67 = squareQ2 inv a b n := by
    simp (disch := decide) only [v67, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v68 : UInt256 := v67 * (n 1)
  let v69 : UInt256 := v68 + v66
  let v70 : UInt256 := UInt256.mulMod v4 (n 3) P
  let v71 : UInt256 := v70 + v61
  let v72 : UInt256 := UInt256.mulMod v21 (n 2) P
  let v73 : UInt256 := v72 + v71
  let v74 : UInt256 := MachineState.readWord (v47) 192
  have eq74 : v74 = squareQ2 inv a b n := by
    simp (disch := decide) only [v74, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v75 : UInt256 := UInt256.mulMod v74 (n 1) P
  let v76 : UInt256 := v75 + v73
  let v77 : UInt256 := MachineState.readWord (v47) 2720
  have eq77 : v77 = inv := by
    simp (disch := decide) only [v77, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v78 : UInt256 := v69 * v77
  let v79 : UInt256 := UInt256.land (UInt256.ofNat (2^240-1)) v78
  have eq79 : v79 = squareQ3 inv a b n := by
    simp (disch := decide) only [v53, v54, v55, v56, v62, v63, v64, v65, v66, v68, v69, v78, v79, eq4, eq21, eq50, eq51, eq52, eq67, eq77, squareQ3, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v80 : ByteArray := MachineState.writeBytes v47 (Data.Bytes.natToBytesPadded v79.toNat 32) 0
  have eq80 : v80 = MachineState.writeBytes v47 (Data.Bytes.natToBytesPadded (squareQ3 inv a b n).toNat 32) 0 := by
    simp (disch := decide) only [v80, eq79, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v81 : UInt256 := UInt256.mulMod v79 (n 0) P
  let v82 : UInt256 := v81 + v76
  let v83 : UInt256 := UInt256.mulMod (UInt256.ofNat 2048) v82 P
  have eq83 : v83 = squareC4 inv a b n := by
    simp (disch := decide) only [v57, v58, v59, v60, v61, v70, v71, v72, v73, v75, v76, v81, v82, v83, eq4, eq21, eq50, eq51, eq52, eq74, eq79, squareC4, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v84 : UInt256 := MachineState.readWord (v80) 64
  have eq84 : v84 = a 4 := by
    simp (disch := decide) only [v84, eq80, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v85 : UInt256 := MachineState.readWord (v80) 768
  have eq85 : v85 = a 0 := by
    simp (disch := decide) only [v85, eq80, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v86 : UInt256 := v84 * v85
  let v87 : UInt256 := MachineState.readWord (v80) 32
  have eq87 : v87 = a 3 := by
    simp (disch := decide) only [v87, eq80, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v88 : UInt256 := (a 1) * v87
  let v89 : UInt256 := v88 + v86
  let v90 : UInt256 := v89 + v89
  let v91 : UInt256 := UInt256.mulMod v84 v85 P
  let v92 : UInt256 := MachineState.readWord (v80) 32
  have eq92 : v92 = a 3 := by
    simp (disch := decide) only [v92, eq80, eq47, readStore, readWord_writeWord, h.at768, h.at2720, h.at32, h.at64, DoubleInput.low_double]
  let v93 : UInt256 := UInt256.mulMod (a 1) v92 P
  change {s with pc := UInt256.ofNat 5968,memory := v80, stack := v93 :: v91 :: v90 :: v83 :: (n 2) :: (n 6) :: (n 4) :: (a 1) :: (a 2) :: (n 5) :: v21 :: P :: v4 :: (n 1) :: (UInt256.ofNat (2^240-1)) :: (n 0) :: (n 3) :: (a 8) :: rest} = _
  simp only [v1, v3, v5, v6, v7, v10, v11, v13, v14, v15, v16, v17, v18, v20, v22, v23, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v45, v48, v49, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v68, v69, v70, v71, v72, v73, v75, v76, v78, v81, v82, v86, v88, v89, v90, v91, v93, eq0, eq2, eq4, eq8, eq9, eq12, eq19, eq21, eq24, eq25, eq44, eq46, eq47, eq50, eq51, eq52, eq67, eq74, eq77, eq79, eq80, eq83, eq84, eq85, eq87, eq92, result1, result0, cells1, cells0, storeCells, writeCell, frame2]
  all_goals rfl

/-- One exact execution theorem replaces both historical column calls. -/
theorem run01 (s : State) (inv : UInt256) (a b n : Nat → UInt256)
    (rest : List UInt256) (h : Memory0 s.memory inv a b n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha0 : (a 0).toNat < radix) :
    runInstructions DoubleInput01.mergedProgram
      {s with pc := UInt256.ofNat 5712, stack := frame0 inv a b n rest} =
        some (result1 (result0 s inv a b n rest) inv a b n rest) := by
  have hx := DoubleInput01.merged_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5)
    (n 7) P (n 8) (n 1) (UInt256.ofNat (2^240-1)) (n 0) (n 3) (a 8) rest
    hcap hact rfl (by rw [h.at768]; exact ha0)
  rw [model01_eq s inv a b n rest h ha0] at hx
  exact hx

/-- The unchanged historical memory interface after the fused execution. -/
theorem memory01_output (s : State) (inv : UInt256) (a b n : Nat → UInt256)
    (rest : List UInt256) (h : Memory0 s.memory inv a b n) :
    Memory2 (result1 (result0 s inv a b n rest) inv a b n rest).memory inv a b n :=
  memory1_output (result0 s inv a b n rest) inv a b n rest
    (memory0_output s inv a b n rest h)

#print axioms model01_eq
#print axioms run01
end CycleSubmission.SquareMeaning

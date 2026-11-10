import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Contracts
import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Memory
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R9InvCompactComplete
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open R9SharedMemory CycleSubmission.Prepared.Arithmetic R5SharedTools Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
def historyMemory (mem : ByteArray) (inv : W) (a b n : Nat → W) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (mem) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ2 inv a b n)).toNat 32) 192) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ3 inv a b n)).toNat 32) 0) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ4 inv a b n)).toNat 32) 224) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ5 inv a b n)).toNat 32) 1216) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ6 inv a b n)).toNat 32) 1248) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ1 inv a b n)).toNat 32) 1088) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ7 inv a b n)).toNat 32) 1280) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD0 inv a b n)).toNat 32) 768) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD1 inv a b n)).toNat 32) 800) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD2 inv a b n)).toNat 32) 832) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD3 inv a b n)).toNat 32) 32) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD4 inv a b n)).toNat 32) 64) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD5 inv a b n)).toNat 32) 96) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD6 inv a b n)).toNat 32) 128) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD7 inv a b n)).toNat 32) 160
def newMemory (mem : ByteArray) (inv : W) (a b n : Nat → W) : ByteArray :=
  MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (MachineState.writeBytes (mem) (Data.Bytes.natToBytesPadded (((a 0))+((a 0))).toNat 32) 768) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ2 inv a b n)).toNat 32) 192) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ3 inv a b n)).toNat 32) 0) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ4 inv a b n)).toNat 32) 224) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ5 inv a b n)).toNat 32) 1216) (Data.Bytes.natToBytesPadded (((a 3))+((a 3))).toNat 32) 32) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ6 inv a b n)).toNat 32) 1248) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ1 inv a b n)).toNat 32) 1088) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareQ7 inv a b n)).toNat 32) 1280) (Data.Bytes.natToBytesPadded (((a 4))+((a 4))).toNat 32) 64) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD0 inv a b n)).toNat 32) 768) (Data.Bytes.natToBytesPadded (((a 5))+((a 5))).toNat 32) 96) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD1 inv a b n)).toNat 32) 800) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD2 inv a b n)).toNat 32) 832) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD3 inv a b n)).toNat 32) 32) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD4 inv a b n)).toNat 32) 64) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD5 inv a b n)).toNat 32) 96) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD6 inv a b n)).toNat 32) 128) (Data.Bytes.natToBytesPadded ((CycleSubmission.WordHistory.squareD7 inv a b n)).toNat 32) 160
theorem memory_same (mem : ByteArray) (inv : W) (a b n : Nat → W) :
    newMemory mem inv a b n = historyMemory mem inv a b n := by
  unfold newMemory historyMemory
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ2 inv a b n)) 768 192 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ3 inv a b n)) 768 0 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ4 inv a b n)) 768 224 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ5 inv a b n)) 768 1216 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) (((a 3))+((a 3))) 768 32 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ6 inv a b n)) 768 1248 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ1 inv a b n)) 768 1088 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareQ7 inv a b n)) 768 1280 (by decide)]
  rw [word_commute _ (((a 0))+((a 0))) (((a 4))+((a 4))) 768 64 (by decide)]
  rw [word_overwrite _ (((a 0))+((a 0))) ((CycleSubmission.WordHistory.squareD0 inv a b n)) 768]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareQ6 inv a b n)) 32 1248 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareQ1 inv a b n)) 32 1088 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareQ7 inv a b n)) 32 1280 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) (((a 4))+((a 4))) 32 64 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareD0 inv a b n)) 32 768 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) (((a 5))+((a 5))) 32 96 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareD1 inv a b n)) 32 800 (by decide)]
  rw [word_commute _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareD2 inv a b n)) 32 832 (by decide)]
  rw [word_overwrite _ (((a 3))+((a 3))) ((CycleSubmission.WordHistory.squareD3 inv a b n)) 32]
  rw [word_commute _ (((a 4))+((a 4))) ((CycleSubmission.WordHistory.squareD0 inv a b n)) 64 768 (by decide)]
  rw [word_commute _ (((a 4))+((a 4))) (((a 5))+((a 5))) 64 96 (by decide)]
  rw [word_commute _ (((a 4))+((a 4))) ((CycleSubmission.WordHistory.squareD1 inv a b n)) 64 800 (by decide)]
  rw [word_commute _ (((a 4))+((a 4))) ((CycleSubmission.WordHistory.squareD2 inv a b n)) 64 832 (by decide)]
  rw [word_commute _ (((a 4))+((a 4))) ((CycleSubmission.WordHistory.squareD3 inv a b n)) 64 32 (by decide)]
  rw [word_overwrite _ (((a 4))+((a 4))) ((CycleSubmission.WordHistory.squareD4 inv a b n)) 64]
  rw [word_commute _ (((a 5))+((a 5))) ((CycleSubmission.WordHistory.squareD1 inv a b n)) 96 800 (by decide)]
  rw [word_commute _ (((a 5))+((a 5))) ((CycleSubmission.WordHistory.squareD2 inv a b n)) 96 832 (by decide)]
  rw [word_commute _ (((a 5))+((a 5))) ((CycleSubmission.WordHistory.squareD3 inv a b n)) 96 32 (by decide)]
  rw [word_commute _ (((a 5))+((a 5))) ((CycleSubmission.WordHistory.squareD4 inv a b n)) 96 64 (by decide)]
  rw [word_overwrite _ (((a 5))+((a 5))) ((CycleSubmission.WordHistory.squareD5 inv a b n)) 96]

def program : List Instr := (R9InvCompactExec.stage0Program ++ (R9InvCompactExec.stage1Program ++ (R9InvCompactExec.stage2Program ++ (R9InvCompactExec.stage3Program ++ (R9InvCompactExec.stage4Program ++ (R9InvCompactExec.stage5Program ++ (R9InvCompactExec.stage6Program ++ (R9InvCompactExec.stage7Program ++ (R9InvCompactExec.stage8Program ++ (R9InvCompactExec.stage9Program ++ (R9InvCompactExec.stage10Program ++ (R9InvCompactExec.stage11Program ++ (R9InvCompactExec.stage12Program ++ (R9InvCompactExec.stage13Program ++ (R9InvCompactExec.stage14Program ++ (R9InvCompactExec.stage15Program ++ (R9InvCompactExec.stage16Program ++ (R9InvCompactExec.stage17Program))))))))))))))))))
theorem run (s : State) (inv : W) (a b n : Nat → W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (hmem : CycleSubmission.SquareMeaning.Memory0 s.memory inv a b n)
    (ha : ∀ i < 8, (a i).toNat < 2^240) :
    runInstructions program {s with pc := N 5568, stack := CycleSubmission.SquareMeaning.frame0 inv a b n rest} =
      some {s with pc := N 7657, memory := historyMemory s.memory inv a b n, stack := CycleSubmission.SquareMeaning.frame15 inv a b n rest} := by
  let p : W := CycleSubmission.WordArithmetic.P
  let C0 : W := CycleSubmission.WordHistory.squareC0 inv a b n
  let C1 : W := CycleSubmission.WordHistory.squareC1 inv a b n
  let C2 : W := CycleSubmission.WordHistory.squareC2 inv a b n
  let C3 : W := CycleSubmission.WordHistory.squareC3 inv a b n
  let C4 : W := CycleSubmission.WordHistory.squareC4 inv a b n
  let C5 : W := CycleSubmission.WordHistory.squareC5 inv a b n
  let C6 : W := CycleSubmission.WordHistory.squareC6 inv a b n
  let C7 : W := CycleSubmission.WordHistory.squareC7 inv a b n
  let C8 : W := CycleSubmission.WordHistory.squareC8 inv a b n
  let C9 : W := CycleSubmission.WordHistory.squareC9 inv a b n
  let C10 : W := CycleSubmission.WordHistory.squareC10 inv a b n
  let C11 : W := CycleSubmission.WordHistory.squareC11 inv a b n
  let C12 : W := CycleSubmission.WordHistory.squareC12 inv a b n
  let C13 : W := CycleSubmission.WordHistory.squareC13 inv a b n
  let C14 : W := CycleSubmission.WordHistory.squareC14 inv a b n
  let C15 : W := CycleSubmission.WordHistory.squareC15 inv a b n
  let C16 : W := CycleSubmission.WordHistory.squareC16 inv a b n
  let C17 : W := CycleSubmission.WordHistory.squareC17 inv a b n
  let Q0 : W := CycleSubmission.WordHistory.squareQ0 inv a b n
  let Q1 : W := CycleSubmission.WordHistory.squareQ1 inv a b n
  let Q2 : W := CycleSubmission.WordHistory.squareQ2 inv a b n
  let Q3 : W := CycleSubmission.WordHistory.squareQ3 inv a b n
  let Q4 : W := CycleSubmission.WordHistory.squareQ4 inv a b n
  let Q5 : W := CycleSubmission.WordHistory.squareQ5 inv a b n
  let Q6 : W := CycleSubmission.WordHistory.squareQ6 inv a b n
  let Q7 : W := CycleSubmission.WordHistory.squareQ7 inv a b n
  let Q8 : W := CycleSubmission.WordHistory.squareQ8 inv a b n
  let Z0 : W := CycleSubmission.WordHistory.squareD0 inv a b n
  let Z1 : W := CycleSubmission.WordHistory.squareD1 inv a b n
  let Z2 : W := CycleSubmission.WordHistory.squareD2 inv a b n
  let Z3 : W := CycleSubmission.WordHistory.squareD3 inv a b n
  let Z4 : W := CycleSubmission.WordHistory.squareD4 inv a b n
  let Z5 : W := CycleSubmission.WordHistory.squareD5 inv a b n
  let Z6 : W := CycleSubmission.WordHistory.squareD6 inv a b n
  let Z7 : W := CycleSubmission.WordHistory.squareD7 inv a b n
  have hp0 : 0 < p.toNat := by
    change 0 < CycleSubmission.WordArithmetic.P.toNat
    rw [CycleSubmission.WordArithmetic.pValue]
    norm_num [HistoricalSearch.CRTColumn.residueModulus]
  have hb0 : C0.toNat < p.toNat := by
    exact hp0
  have hb1 : C1.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb2 : C2.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb3 : C3.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb4 : C4.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb5 : C5.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb6 : C6.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb7 : C7.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb8 : C8.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb9 : C9.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb10 : C10.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb11 : C11.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb12 : C12.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb13 : C13.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb14 : C14.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb15 : C15.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb16 : C16.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hb17 : C17.toNat < p.toNat := by
    change (UInt256.mulMod _ _ p).toNat < p.toNat
    exact residue_lt _ _ _ hp0
  have hq0 : R9SharedMath0.qNew ((a 0)) ((n 0)) (p) (inv) = Q0 := by
    exact R9SharedMath0.old_q_matches inv a b n
  have hc0 : R9SharedMath0.cNew ((a 0)) ((n 0)) (p) (inv) = C1 := by
    exact R9SharedMath0.old_c_matches inv a b n
  have hq1 : R9SharedMath1.qNew (C1) (Q0) ((a 0)) ((a 1)) ((n 0)) ((n 1)) (p) (inv) = Q1 := by
    exact (R9SharedMath1.q_same (C1) (Q0) ((a 0)) ((a 1)) ((n 0)) ((n 1)) (p) (inv)).trans (R9SharedMath1.old_q_matches inv a b n)
  have hc1 : R9SharedMath1.cNew (C1) (Q0) ((a 0)) ((a 1)) ((n 0)) ((n 1)) (p) (inv) = C2 := by
    exact (R9SharedMath1.c_same (C1) (Q0) ((a 0)) ((a 1)) ((n 0)) ((n 1)) (p) (inv) (ha 0 (by decide)) rfl hb1).trans (R9SharedMath1.old_c_matches inv a b n)
  have hq2 : R9SharedMath2.qNew (C2) (Q0) (Q1) ((a 0)) ((a 1)) ((a 2)) ((n 0)) ((n 1)) ((n 2)) (p) (inv) = Q2 := by
    exact (R9SharedMath2.q_same (C2) (Q0) (Q1) ((a 0)) ((a 1)) ((a 2)) ((n 0)) ((n 1)) ((n 2)) (p) (inv)).trans (R9SharedMath2.old_q_matches inv a b n)
  have hc2 : R9SharedMath2.cNew (C2) (Q0) (Q1) ((a 0)) ((a 1)) ((a 2)) ((n 0)) ((n 1)) ((n 2)) (p) (inv) = C3 := by
    exact (R9SharedMath2.c_same (C2) (Q0) (Q1) ((a 0)) ((a 1)) ((a 2)) ((n 0)) ((n 1)) ((n 2)) (p) (inv) (ha 0 (by decide)) rfl hb2).trans (R9SharedMath2.old_c_matches inv a b n)
  have hq3 : R9SharedMath3.qNew (C3) (Q0) (Q1) (Q2) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) (p) (inv) = Q3 := by
    exact (R9SharedMath3.q_same (C3) (Q0) (Q1) (Q2) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) (p) (inv)).trans (R9SharedMath3.old_q_matches inv a b n)
  have hc3 : R9SharedMath3.cNew (C3) (Q0) (Q1) (Q2) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) (p) (inv) = C4 := by
    exact (R9SharedMath3.c_same (C3) (Q0) (Q1) (Q2) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) rfl hb3).trans (R9SharedMath3.old_c_matches inv a b n)
  have hq4 : R9SharedMath4.qNew (C4) (Q0) (Q1) (Q2) (Q3) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) (p) (inv) = Q4 := by
    exact (R9SharedMath4.q_same (C4) (Q0) (Q1) (Q2) (Q3) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) (p) (inv)).trans (R9SharedMath4.old_q_matches inv a b n)
  have hc4 : R9SharedMath4.cNew (C4) (Q0) (Q1) (Q2) (Q3) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) (p) (inv) = C5 := by
    exact (R9SharedMath4.c_same (C4) (Q0) (Q1) (Q2) (Q3) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) rfl hb4).trans (R9SharedMath4.old_c_matches inv a b n)
  have hq5 : R9SharedMath5.qNew (C5) (Q0) (Q1) (Q2) (Q3) (Q4) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) (p) (inv) = Q5 := by
    exact (R9SharedMath5.q_same (C5) (Q0) (Q1) (Q2) (Q3) (Q4) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) (p) (inv)).trans (R9SharedMath5.old_q_matches inv a b n)
  have hc5 : R9SharedMath5.cNew (C5) (Q0) (Q1) (Q2) (Q3) (Q4) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) (p) (inv) = C6 := by
    exact (R9SharedMath5.c_same (C5) (Q0) (Q1) (Q2) (Q3) (Q4) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) rfl hb5).trans (R9SharedMath5.old_c_matches inv a b n)
  have hq6 : R9SharedMath6.qNew (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) (p) (inv) = Q6 := by
    exact (R9SharedMath6.q_same (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) (p) (inv)).trans (R9SharedMath6.old_q_matches inv a b n)
  have hc6 : R9SharedMath6.cNew (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) (p) (inv) = C7 := by
    exact (R9SharedMath6.c_same (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) rfl hb6).trans (R9SharedMath6.old_c_matches inv a b n)
  have hq7 : R9SharedMath7.qNew (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) (p) (inv) = Q7 := by
    exact (R9SharedMath7.q_same (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) (p) (inv)).trans (R9SharedMath7.old_q_matches inv a b n)
  have hc7 : R9SharedMath7.cNew (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) (p) (inv) = C8 := by
    exact (R9SharedMath7.c_same (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide)) rfl hb7).trans (R9SharedMath7.old_c_matches inv a b n)
  have hq8 : R9SharedMath8.qNew (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) = Q8 := by
    exact (R9SharedMath8.q_same (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv)).trans (R9SharedMath8.old_q_matches inv a b n)
  have hc8 : R9SharedMath8.cNew (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) = C9 := by
    exact (R9SharedMath8.c_same (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) (ha 0 (by decide)) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide)) rfl hb8).trans (R9SharedMath8.old_c_matches inv a b n)
  have hq9 : R9SharedMath9.qNew (C9) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = Z0 := by
    exact (R9SharedMath9.q_same (C9) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath9.old_q_matches inv a b n)
  have hc9 : R9SharedMath9.cNew (C9) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = C10 := by
    exact (R9SharedMath9.c_same (C9) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 1 (by decide)) (ha 2 (by decide)) (ha 3 (by decide)) (ha 4 (by decide)) rfl hb9).trans (R9SharedMath9.old_c_matches inv a b n)
  have hq10 : R9SharedMath10.qNew (C10) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = Z1 := by
    exact (R9SharedMath10.q_same (C10) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath10.old_q_matches inv a b n)
  have hc10 : R9SharedMath10.cNew (C10) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = C11 := by
    exact (R9SharedMath10.c_same (C10) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 2 (by decide)) (ha 3 (by decide)) (ha 4 (by decide)) rfl hb10).trans (R9SharedMath10.old_c_matches inv a b n)
  have hq11 : R9SharedMath11.qNew (C11) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = Z2 := by
    exact (R9SharedMath11.q_same (C11) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath11.old_q_matches inv a b n)
  have hc11 : R9SharedMath11.cNew (C11) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = C12 := by
    exact (R9SharedMath11.c_same (C11) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 3 (by decide)) (ha 4 (by decide)) (ha 5 (by decide)) rfl hb11).trans (R9SharedMath11.old_c_matches inv a b n)
  have hq12 : R9SharedMath12.qNew (C12) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = Z3 := by
    exact (R9SharedMath12.q_same (C12) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath12.old_q_matches inv a b n)
  have hc12 : R9SharedMath12.cNew (C12) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = C13 := by
    exact (R9SharedMath12.c_same (C12) (Q4) (Q5) (Q6) (Q7) (Q8) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 4 (by decide)) (ha 5 (by decide)) rfl hb12).trans (R9SharedMath12.old_c_matches inv a b n)
  have hq13 : R9SharedMath13.qNew (C13) (Q5) (Q6) (Q7) (Q8) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = Z4 := by
    exact (R9SharedMath13.q_same (C13) (Q5) (Q6) (Q7) (Q8) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath13.old_q_matches inv a b n)
  have hc13 : R9SharedMath13.cNew (C13) (Q5) (Q6) (Q7) (Q8) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) = C14 := by
    exact (R9SharedMath13.c_same (C13) (Q5) (Q6) (Q7) (Q8) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 5 (by decide)) (ha 6 (by decide)) rfl hb13).trans (R9SharedMath13.old_c_matches inv a b n)
  have hq14 : R9SharedMath14.qNew (C14) (Q6) (Q7) (Q8) ((a 6)) ((a 7)) ((a 8)) ((n 6)) ((n 7)) ((n 8)) (p) = Z5 := by
    exact (R9SharedMath14.q_same (C14) (Q6) (Q7) (Q8) ((a 6)) ((a 7)) ((a 8)) ((n 6)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath14.old_q_matches inv a b n)
  have hc14 : R9SharedMath14.cNew (C14) (Q6) (Q7) (Q8) ((a 6)) ((a 7)) ((a 8)) ((n 6)) ((n 7)) ((n 8)) (p) = C15 := by
    exact (R9SharedMath14.c_same (C14) (Q6) (Q7) (Q8) ((a 6)) ((a 7)) ((a 8)) ((n 6)) ((n 7)) ((n 8)) (p) (ha 6 (by decide)) rfl hb14).trans (R9SharedMath14.old_c_matches inv a b n)
  have hq15 : R9SharedMath15.qNew (C15) (Q7) (Q8) ((a 7)) ((a 8)) ((n 7)) ((n 8)) (p) = Z6 := by
    exact (R9SharedMath15.q_same (C15) (Q7) (Q8) ((a 7)) ((a 8)) ((n 7)) ((n 8)) (p)).trans (R9SharedMath15.old_q_matches inv a b n)
  have hc15 : R9SharedMath15.cNew (C15) (Q7) (Q8) ((a 7)) ((a 8)) ((n 7)) ((n 8)) (p) = C16 := by
    exact (R9SharedMath15.c_same (C15) (Q7) (Q8) ((a 7)) ((a 8)) ((n 7)) ((n 8)) (p) (ha 7 (by decide)) rfl hb15).trans (R9SharedMath15.old_c_matches inv a b n)
  have hq16 : R9SharedMath16.qNew (C16) (Q8) ((a 8)) ((n 8)) (p) = Z7 := by
    exact R9SharedMath16.old_q_matches inv a b n
  have hc16 : R9SharedMath16.cNew (C16) (Q8) ((a 8)) ((n 8)) (p) = C17 := by
    exact R9SharedMath16.old_c_matches inv a b n
  let M0 : ByteArray := s.memory
  have hm0_768 : MachineState.readWord M0 768 = (a 0) := hmem.at768
  have hm0_32 : MachineState.readWord M0 32 = (a 3) := hmem.at32
  have hm0_64 : MachineState.readWord M0 64 = (a 4) := hmem.at64
  have hm0_96 : MachineState.readWord M0 96 = (a 5) := hmem.at96
  have hm0_128 : MachineState.readWord M0 128 = (a 6) := hmem.at128
  have hm0_160 : MachineState.readWord M0 160 = (a 7) := hmem.at160
  have hm0_2720 : MachineState.readWord M0 2720 = inv := hmem.at2720
  have hm0_1344 : MachineState.readWord M0 1344 = (n 0) := hmem.at1344
  have hm0_1376 : MachineState.readWord M0 1376 = (n 1) := hmem.at1376
  have hm0_1568 : MachineState.readWord M0 1568 = (n 7) := hmem.at1568
  have hm0_1600 : MachineState.readWord M0 1600 = (n 8) := hmem.at1600
  let M1 : ByteArray := M0
  have h0 : runInstructions R9InvCompactExec.stage0Program {s with pc := N 5568, memory := M0, stack := ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N (2^240-1)) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 5631, memory := M1, stack := (C1) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: ((n 7)) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M1] using R9InvCompactContracts.stage0_history ({s with memory := M0}) (C0) (C1) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm0_768 hm0_32 hm0_64 hm0_96 hm0_128 hm0_160 hm0_2720 hm0_1344 hm0_1376 hm0_1568 hm0_1600 hq0 hc0
  have hm1_768 : MachineState.readWord M1 768 = (a 0) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_768]
  have hm1_32 : MachineState.readWord M1 32 = (a 3) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_32]
  have hm1_64 : MachineState.readWord M1 64 = (a 4) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_64]
  have hm1_96 : MachineState.readWord M1 96 = (a 5) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_96]
  have hm1_128 : MachineState.readWord M1 128 = (a 6) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_128]
  have hm1_160 : MachineState.readWord M1 160 = (a 7) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_160]
  have hm1_2720 : MachineState.readWord M1 2720 = inv := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_2720]
  have hm1_1344 : MachineState.readWord M1 1344 = (n 0) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_1344]
  have hm1_1376 : MachineState.readWord M1 1376 = (n 1) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_1376]
  have hm1_1568 : MachineState.readWord M1 1568 = (n 7) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_1568]
  have hm1_1600 : MachineState.readWord M1 1600 = (n 8) := by
    simp (disch := decide) only [M1, readWord_writeWord, read_disjoint, hm0_1600]
  let M2 : ByteArray := MachineState.writeBytes (M1) (Data.Bytes.natToBytesPadded (((a 0))+((a 0))).toNat 32) 768
  have h1 : runInstructions R9InvCompactExec.stage1Program {s with pc := N 5631, memory := M1, stack := (C1) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: ((n 7)) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 5709, memory := M2, stack := (C2) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M2] using R9InvCompactContracts.stage1_history ({s with memory := M1}) (C1) (C2) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm1_768 hm1_32 hm1_64 hm1_96 hm1_128 hm1_160 hm1_2720 hm1_1344 hm1_1376 hm1_1568 hm1_1600 hq1 hc1
  have hm2_768 : MachineState.readWord M2 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_768]
  have hm2_32 : MachineState.readWord M2 32 = (a 3) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_32]
  have hm2_64 : MachineState.readWord M2 64 = (a 4) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_64]
  have hm2_96 : MachineState.readWord M2 96 = (a 5) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_96]
  have hm2_128 : MachineState.readWord M2 128 = (a 6) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_128]
  have hm2_160 : MachineState.readWord M2 160 = (a 7) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_160]
  have hm2_2720 : MachineState.readWord M2 2720 = inv := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_2720]
  have hm2_1344 : MachineState.readWord M2 1344 = (n 0) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_1344]
  have hm2_1376 : MachineState.readWord M2 1376 = (n 1) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_1376]
  have hm2_1568 : MachineState.readWord M2 1568 = (n 7) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_1568]
  have hm2_1600 : MachineState.readWord M2 1600 = (n 8) := by
    simp (disch := decide) only [M2, readWord_writeWord, read_disjoint, hm1_1600]
  let M3 : ByteArray := MachineState.writeBytes (M2) (Data.Bytes.natToBytesPadded (Q2).toNat 32) 192
  have h2 : runInstructions R9InvCompactExec.stage2Program {s with pc := N 5709, memory := M2, stack := (C2) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 5802, memory := M3, stack := (C3) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M3] using R9InvCompactContracts.stage2_history ({s with memory := M2}) (C2) (C3) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm2_768 hm2_32 hm2_64 hm2_96 hm2_128 hm2_160 hm2_2720 hm2_1344 hm2_1376 hm2_1568 hm2_1600 hq2 hc2
  have hm3_768 : MachineState.readWord M3 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_768]
  have hm3_32 : MachineState.readWord M3 32 = (a 3) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_32]
  have hm3_64 : MachineState.readWord M3 64 = (a 4) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_64]
  have hm3_96 : MachineState.readWord M3 96 = (a 5) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_96]
  have hm3_128 : MachineState.readWord M3 128 = (a 6) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_128]
  have hm3_160 : MachineState.readWord M3 160 = (a 7) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_160]
  have hm3_2720 : MachineState.readWord M3 2720 = inv := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_2720]
  have hm3_1344 : MachineState.readWord M3 1344 = (n 0) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_1344]
  have hm3_1376 : MachineState.readWord M3 1376 = (n 1) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_1376]
  have hm3_1568 : MachineState.readWord M3 1568 = (n 7) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_1568]
  have hm3_1600 : MachineState.readWord M3 1600 = (n 8) := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint, hm2_1600]
  have hm3_192 : MachineState.readWord M3 192 = Q2 := by
    simp (disch := decide) only [M3, readWord_writeWord, read_disjoint]
  let M4 : ByteArray := MachineState.writeBytes (M3) (Data.Bytes.natToBytesPadded (Q3).toNat 32) 0
  have h3 : runInstructions R9InvCompactExec.stage3Program {s with pc := N 5802, memory := M3, stack := (C3) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 5907, memory := M4, stack := (C4) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M4] using R9InvCompactContracts.stage3_history ({s with memory := M3}) (C3) (C4) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm3_768 hm3_32 hm3_64 hm3_96 hm3_128 hm3_160 hm3_2720 hm3_1344 hm3_1376 hm3_1568 hm3_1600 hm3_192 hq3 hc3
  have hm4_768 : MachineState.readWord M4 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_768]
  have hm4_32 : MachineState.readWord M4 32 = (a 3) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_32]
  have hm4_64 : MachineState.readWord M4 64 = (a 4) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_64]
  have hm4_96 : MachineState.readWord M4 96 = (a 5) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_96]
  have hm4_128 : MachineState.readWord M4 128 = (a 6) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_128]
  have hm4_160 : MachineState.readWord M4 160 = (a 7) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_160]
  have hm4_2720 : MachineState.readWord M4 2720 = inv := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_2720]
  have hm4_1344 : MachineState.readWord M4 1344 = (n 0) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_1344]
  have hm4_1376 : MachineState.readWord M4 1376 = (n 1) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_1376]
  have hm4_1568 : MachineState.readWord M4 1568 = (n 7) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_1568]
  have hm4_1600 : MachineState.readWord M4 1600 = (n 8) := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_1600]
  have hm4_192 : MachineState.readWord M4 192 = Q2 := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint, hm3_192]
  have hm4_0 : MachineState.readWord M4 0 = Q3 := by
    simp (disch := decide) only [M4, readWord_writeWord, read_disjoint]
  let M5 : ByteArray := MachineState.writeBytes (M4) (Data.Bytes.natToBytesPadded (Q4).toNat 32) 224
  have h4 : runInstructions R9InvCompactExec.stage4Program {s with pc := N 5907, memory := M4, stack := (C4) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: ((a 2)) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6040, memory := M5, stack := (C5) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M5] using R9InvCompactContracts.stage4_history ({s with memory := M4}) (C4) (C5) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm4_768 hm4_32 hm4_64 hm4_96 hm4_128 hm4_160 hm4_2720 hm4_1344 hm4_1376 hm4_1568 hm4_1600 hm4_192 hm4_0 hq4 hc4
  have hm5_768 : MachineState.readWord M5 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_768]
  have hm5_32 : MachineState.readWord M5 32 = (a 3) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_32]
  have hm5_64 : MachineState.readWord M5 64 = (a 4) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_64]
  have hm5_96 : MachineState.readWord M5 96 = (a 5) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_96]
  have hm5_128 : MachineState.readWord M5 128 = (a 6) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_128]
  have hm5_160 : MachineState.readWord M5 160 = (a 7) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_160]
  have hm5_2720 : MachineState.readWord M5 2720 = inv := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_2720]
  have hm5_1344 : MachineState.readWord M5 1344 = (n 0) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_1344]
  have hm5_1376 : MachineState.readWord M5 1376 = (n 1) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_1376]
  have hm5_1568 : MachineState.readWord M5 1568 = (n 7) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_1568]
  have hm5_1600 : MachineState.readWord M5 1600 = (n 8) := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_1600]
  have hm5_192 : MachineState.readWord M5 192 = Q2 := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_192]
  have hm5_0 : MachineState.readWord M5 0 = Q3 := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint, hm4_0]
  have hm5_224 : MachineState.readWord M5 224 = Q4 := by
    simp (disch := decide) only [M5, readWord_writeWord, read_disjoint]
  let M6 : ByteArray := MachineState.writeBytes (M5) (Data.Bytes.natToBytesPadded (Q5).toNat 32) 1216
  have h5 : runInstructions R9InvCompactExec.stage5Program {s with pc := N 6040, memory := M5, stack := (C5) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6188, memory := M6, stack := (C6) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M6] using R9InvCompactContracts.stage5_history ({s with memory := M5}) (C5) (C6) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm5_768 hm5_32 hm5_64 hm5_96 hm5_128 hm5_160 hm5_2720 hm5_1344 hm5_1376 hm5_1568 hm5_1600 hm5_192 hm5_0 hm5_224 hq5 hc5
  have hm6_768 : MachineState.readWord M6 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_768]
  have hm6_32 : MachineState.readWord M6 32 = (a 3) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_32]
  have hm6_64 : MachineState.readWord M6 64 = (a 4) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_64]
  have hm6_96 : MachineState.readWord M6 96 = (a 5) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_96]
  have hm6_128 : MachineState.readWord M6 128 = (a 6) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_128]
  have hm6_160 : MachineState.readWord M6 160 = (a 7) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_160]
  have hm6_2720 : MachineState.readWord M6 2720 = inv := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_2720]
  have hm6_1344 : MachineState.readWord M6 1344 = (n 0) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_1344]
  have hm6_1376 : MachineState.readWord M6 1376 = (n 1) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_1376]
  have hm6_1568 : MachineState.readWord M6 1568 = (n 7) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_1568]
  have hm6_1600 : MachineState.readWord M6 1600 = (n 8) := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_1600]
  have hm6_192 : MachineState.readWord M6 192 = Q2 := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_192]
  have hm6_0 : MachineState.readWord M6 0 = Q3 := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_0]
  have hm6_224 : MachineState.readWord M6 224 = Q4 := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint, hm5_224]
  have hm6_1216 : MachineState.readWord M6 1216 = Q5 := by
    simp (disch := decide) only [M6, readWord_writeWord, read_disjoint]
  let M7 : ByteArray := MachineState.writeBytes (MachineState.writeBytes (M6) (Data.Bytes.natToBytesPadded (((a 3))+((a 3))).toNat 32) 32) (Data.Bytes.natToBytesPadded (Q6).toNat 32) 1248
  have h6 : runInstructions R9InvCompactExec.stage6Program {s with pc := N 6188, memory := M6, stack := (C6) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6370, memory := M7, stack := (C7) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M7] using R9InvCompactContracts.stage6_history ({s with memory := M6}) (C6) (C7) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm6_768 hm6_32 hm6_64 hm6_96 hm6_128 hm6_160 hm6_2720 hm6_1344 hm6_1376 hm6_1568 hm6_1600 hm6_192 hm6_0 hm6_224 hm6_1216 hq6 hc6
  have hm7_768 : MachineState.readWord M7 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_768]
  have hm7_32 : MachineState.readWord M7 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_32]
  have hm7_64 : MachineState.readWord M7 64 = (a 4) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_64]
  have hm7_96 : MachineState.readWord M7 96 = (a 5) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_96]
  have hm7_128 : MachineState.readWord M7 128 = (a 6) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_128]
  have hm7_160 : MachineState.readWord M7 160 = (a 7) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_160]
  have hm7_2720 : MachineState.readWord M7 2720 = inv := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_2720]
  have hm7_1344 : MachineState.readWord M7 1344 = (n 0) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_1344]
  have hm7_1376 : MachineState.readWord M7 1376 = (n 1) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_1376]
  have hm7_1568 : MachineState.readWord M7 1568 = (n 7) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_1568]
  have hm7_1600 : MachineState.readWord M7 1600 = (n 8) := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_1600]
  have hm7_192 : MachineState.readWord M7 192 = Q2 := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_192]
  have hm7_0 : MachineState.readWord M7 0 = Q3 := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_0]
  have hm7_224 : MachineState.readWord M7 224 = Q4 := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_224]
  have hm7_1216 : MachineState.readWord M7 1216 = Q5 := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint, hm6_1216]
  have hm7_1248 : MachineState.readWord M7 1248 = Q6 := by
    simp (disch := decide) only [M7, readWord_writeWord, read_disjoint]
  let M8 : ByteArray := MachineState.writeBytes (MachineState.writeBytes (M7) (Data.Bytes.natToBytesPadded (Q1).toNat 32) 1088) (Data.Bytes.natToBytesPadded (Q7).toNat 32) 1280
  have h7 : runInstructions R9InvCompactExec.stage7Program {s with pc := N 6370, memory := M7, stack := (C7) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: (Q1) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6575, memory := M8, stack := (C8) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M8] using R9InvCompactContracts.stage7_history ({s with memory := M7}) (C7) (C8) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm7_768 hm7_32 hm7_64 hm7_96 hm7_128 hm7_160 hm7_2720 hm7_1344 hm7_1376 hm7_1568 hm7_1600 hm7_192 hm7_0 hm7_224 hm7_1216 hm7_1248 hq7 hc7
  have hm8_768 : MachineState.readWord M8 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_768]
  have hm8_32 : MachineState.readWord M8 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_32]
  have hm8_64 : MachineState.readWord M8 64 = (a 4) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_64]
  have hm8_96 : MachineState.readWord M8 96 = (a 5) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_96]
  have hm8_128 : MachineState.readWord M8 128 = (a 6) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_128]
  have hm8_160 : MachineState.readWord M8 160 = (a 7) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_160]
  have hm8_2720 : MachineState.readWord M8 2720 = inv := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_2720]
  have hm8_1344 : MachineState.readWord M8 1344 = (n 0) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1344]
  have hm8_1376 : MachineState.readWord M8 1376 = (n 1) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1376]
  have hm8_1568 : MachineState.readWord M8 1568 = (n 7) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1568]
  have hm8_1600 : MachineState.readWord M8 1600 = (n 8) := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1600]
  have hm8_192 : MachineState.readWord M8 192 = Q2 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_192]
  have hm8_0 : MachineState.readWord M8 0 = Q3 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_0]
  have hm8_224 : MachineState.readWord M8 224 = Q4 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_224]
  have hm8_1216 : MachineState.readWord M8 1216 = Q5 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1216]
  have hm8_1248 : MachineState.readWord M8 1248 = Q6 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint, hm7_1248]
  have hm8_1088 : MachineState.readWord M8 1088 = Q1 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint]
  have hm8_1280 : MachineState.readWord M8 1280 = Q7 := by
    simp (disch := decide) only [M8, readWord_writeWord, read_disjoint]
  let M9 : ByteArray := MachineState.writeBytes (M8) (Data.Bytes.natToBytesPadded (((a 4))+((a 4))).toNat 32) 64
  have h8 : runInstructions R9InvCompactExec.stage8Program {s with pc := N 6575, memory := M8, stack := (C8) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: (Q0) :: ((n 1)) :: (inv) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6815, memory := M9, stack := (C9) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M9] using R9InvCompactContracts.stage8_history ({s with memory := M8}) (C8) (C9) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm8_768 hm8_32 hm8_64 hm8_96 hm8_128 hm8_160 hm8_2720 hm8_1344 hm8_1376 hm8_1568 hm8_1600 hm8_192 hm8_0 hm8_224 hm8_1216 hm8_1248 hm8_1088 hm8_1280 hq8 hc8
  have hm9_768 : MachineState.readWord M9 768 = ((a 0))+((a 0)) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_768]
  have hm9_32 : MachineState.readWord M9 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_32]
  have hm9_64 : MachineState.readWord M9 64 = ((a 4))+((a 4)) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_64]
  have hm9_96 : MachineState.readWord M9 96 = (a 5) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_96]
  have hm9_128 : MachineState.readWord M9 128 = (a 6) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_128]
  have hm9_160 : MachineState.readWord M9 160 = (a 7) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_160]
  have hm9_2720 : MachineState.readWord M9 2720 = inv := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_2720]
  have hm9_1344 : MachineState.readWord M9 1344 = (n 0) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1344]
  have hm9_1376 : MachineState.readWord M9 1376 = (n 1) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1376]
  have hm9_1568 : MachineState.readWord M9 1568 = (n 7) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1568]
  have hm9_1600 : MachineState.readWord M9 1600 = (n 8) := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1600]
  have hm9_192 : MachineState.readWord M9 192 = Q2 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_192]
  have hm9_0 : MachineState.readWord M9 0 = Q3 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_0]
  have hm9_224 : MachineState.readWord M9 224 = Q4 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_224]
  have hm9_1216 : MachineState.readWord M9 1216 = Q5 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1216]
  have hm9_1248 : MachineState.readWord M9 1248 = Q6 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1248]
  have hm9_1088 : MachineState.readWord M9 1088 = Q1 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1088]
  have hm9_1280 : MachineState.readWord M9 1280 = Q7 := by
    simp (disch := decide) only [M9, readWord_writeWord, read_disjoint, hm8_1280]
  let M10 : ByteArray := MachineState.writeBytes (M9) (Data.Bytes.natToBytesPadded (Z0).toNat 32) 768
  have h9 : runInstructions R9InvCompactExec.stage9Program {s with pc := N 6815, memory := M9, stack := (C9) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (((a 1))+((a 1))) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 6996, memory := M10, stack := (C10) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M10] using R9InvCompactContracts.stage9_history ({s with memory := M9}) (C9) (C10) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm9_768 hm9_32 hm9_64 hm9_96 hm9_128 hm9_160 hm9_2720 hm9_1344 hm9_1376 hm9_1568 hm9_1600 hm9_192 hm9_0 hm9_224 hm9_1216 hm9_1248 hm9_1088 hm9_1280 hq9 hc9
  have hm10_768 : MachineState.readWord M10 768 = Z0 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_768]
  have hm10_32 : MachineState.readWord M10 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_32]
  have hm10_64 : MachineState.readWord M10 64 = ((a 4))+((a 4)) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_64]
  have hm10_96 : MachineState.readWord M10 96 = (a 5) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_96]
  have hm10_128 : MachineState.readWord M10 128 = (a 6) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_128]
  have hm10_160 : MachineState.readWord M10 160 = (a 7) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_160]
  have hm10_2720 : MachineState.readWord M10 2720 = inv := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_2720]
  have hm10_1344 : MachineState.readWord M10 1344 = (n 0) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1344]
  have hm10_1376 : MachineState.readWord M10 1376 = (n 1) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1376]
  have hm10_1568 : MachineState.readWord M10 1568 = (n 7) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1568]
  have hm10_1600 : MachineState.readWord M10 1600 = (n 8) := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1600]
  have hm10_192 : MachineState.readWord M10 192 = Q2 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_192]
  have hm10_0 : MachineState.readWord M10 0 = Q3 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_0]
  have hm10_224 : MachineState.readWord M10 224 = Q4 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_224]
  have hm10_1216 : MachineState.readWord M10 1216 = Q5 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1216]
  have hm10_1248 : MachineState.readWord M10 1248 = Q6 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1248]
  have hm10_1088 : MachineState.readWord M10 1088 = Q1 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1088]
  have hm10_1280 : MachineState.readWord M10 1280 = Q7 := by
    simp (disch := decide) only [M10, readWord_writeWord, read_disjoint, hm9_1280]
  let M11 : ByteArray := MachineState.writeBytes (MachineState.writeBytes (M10) (Data.Bytes.natToBytesPadded (((a 5))+((a 5))).toNat 32) 96) (Data.Bytes.natToBytesPadded (Z1).toNat 32) 800
  have h10 : runInstructions R9InvCompactExec.stage10Program {s with pc := N 6996, memory := M10, stack := (C10) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (((a 2))+((a 2))) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7162, memory := M11, stack := (C11) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M11] using R9InvCompactContracts.stage10_history ({s with memory := M10}) (C10) (C11) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm10_768 hm10_32 hm10_64 hm10_96 hm10_128 hm10_160 hm10_2720 hm10_1344 hm10_1376 hm10_1568 hm10_1600 hm10_192 hm10_0 hm10_224 hm10_1216 hm10_1248 hm10_1088 hm10_1280 hq10 hc10
  have hm11_768 : MachineState.readWord M11 768 = Z0 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_768]
  have hm11_32 : MachineState.readWord M11 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_32]
  have hm11_64 : MachineState.readWord M11 64 = ((a 4))+((a 4)) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_64]
  have hm11_96 : MachineState.readWord M11 96 = ((a 5))+((a 5)) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_96]
  have hm11_128 : MachineState.readWord M11 128 = (a 6) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_128]
  have hm11_160 : MachineState.readWord M11 160 = (a 7) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_160]
  have hm11_2720 : MachineState.readWord M11 2720 = inv := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_2720]
  have hm11_1344 : MachineState.readWord M11 1344 = (n 0) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1344]
  have hm11_1376 : MachineState.readWord M11 1376 = (n 1) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1376]
  have hm11_1568 : MachineState.readWord M11 1568 = (n 7) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1568]
  have hm11_1600 : MachineState.readWord M11 1600 = (n 8) := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1600]
  have hm11_192 : MachineState.readWord M11 192 = Q2 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_192]
  have hm11_0 : MachineState.readWord M11 0 = Q3 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_0]
  have hm11_224 : MachineState.readWord M11 224 = Q4 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_224]
  have hm11_1216 : MachineState.readWord M11 1216 = Q5 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1216]
  have hm11_1248 : MachineState.readWord M11 1248 = Q6 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1248]
  have hm11_1088 : MachineState.readWord M11 1088 = Q1 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1088]
  have hm11_1280 : MachineState.readWord M11 1280 = Q7 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint, hm10_1280]
  have hm11_800 : MachineState.readWord M11 800 = Z1 := by
    simp (disch := decide) only [M11, readWord_writeWord, read_disjoint]
  let M12 : ByteArray := MachineState.writeBytes (M11) (Data.Bytes.natToBytesPadded (Z2).toNat 32) 832
  have h11 : runInstructions R9InvCompactExec.stage11Program {s with pc := N 7162, memory := M11, stack := (C11) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7282, memory := M12, stack := (C12) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M12] using R9InvCompactContracts.stage11_history ({s with memory := M11}) (C11) (C12) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm11_768 hm11_32 hm11_64 hm11_96 hm11_128 hm11_160 hm11_2720 hm11_1344 hm11_1376 hm11_1568 hm11_1600 hm11_192 hm11_0 hm11_224 hm11_1216 hm11_1248 hm11_1088 hm11_1280 hm11_800 hq11 hc11
  have hm12_768 : MachineState.readWord M12 768 = Z0 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_768]
  have hm12_32 : MachineState.readWord M12 32 = ((a 3))+((a 3)) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_32]
  have hm12_64 : MachineState.readWord M12 64 = ((a 4))+((a 4)) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_64]
  have hm12_96 : MachineState.readWord M12 96 = ((a 5))+((a 5)) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_96]
  have hm12_128 : MachineState.readWord M12 128 = (a 6) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_128]
  have hm12_160 : MachineState.readWord M12 160 = (a 7) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_160]
  have hm12_2720 : MachineState.readWord M12 2720 = inv := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_2720]
  have hm12_1344 : MachineState.readWord M12 1344 = (n 0) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1344]
  have hm12_1376 : MachineState.readWord M12 1376 = (n 1) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1376]
  have hm12_1568 : MachineState.readWord M12 1568 = (n 7) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1568]
  have hm12_1600 : MachineState.readWord M12 1600 = (n 8) := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1600]
  have hm12_192 : MachineState.readWord M12 192 = Q2 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_192]
  have hm12_0 : MachineState.readWord M12 0 = Q3 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_0]
  have hm12_224 : MachineState.readWord M12 224 = Q4 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_224]
  have hm12_1216 : MachineState.readWord M12 1216 = Q5 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1216]
  have hm12_1248 : MachineState.readWord M12 1248 = Q6 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1248]
  have hm12_1088 : MachineState.readWord M12 1088 = Q1 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1088]
  have hm12_1280 : MachineState.readWord M12 1280 = Q7 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_1280]
  have hm12_800 : MachineState.readWord M12 800 = Z1 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint, hm11_800]
  have hm12_832 : MachineState.readWord M12 832 = Z2 := by
    simp (disch := decide) only [M12, readWord_writeWord, read_disjoint]
  let M13 : ByteArray := MachineState.writeBytes (M12) (Data.Bytes.natToBytesPadded (Z3).toNat 32) 32
  have h12 : runInstructions R9InvCompactExec.stage12Program {s with pc := N 7282, memory := M12, stack := (C12) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7389, memory := M13, stack := (C13) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M13] using R9InvCompactContracts.stage12_history ({s with memory := M12}) (C12) (C13) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm12_768 hm12_32 hm12_64 hm12_96 hm12_128 hm12_160 hm12_2720 hm12_1344 hm12_1376 hm12_1568 hm12_1600 hm12_192 hm12_0 hm12_224 hm12_1216 hm12_1248 hm12_1088 hm12_1280 hm12_800 hm12_832 hq12 hc12
  have hm13_768 : MachineState.readWord M13 768 = Z0 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_768]
  have hm13_32 : MachineState.readWord M13 32 = Z3 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_32]
  have hm13_64 : MachineState.readWord M13 64 = ((a 4))+((a 4)) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_64]
  have hm13_96 : MachineState.readWord M13 96 = ((a 5))+((a 5)) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_96]
  have hm13_128 : MachineState.readWord M13 128 = (a 6) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_128]
  have hm13_160 : MachineState.readWord M13 160 = (a 7) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_160]
  have hm13_2720 : MachineState.readWord M13 2720 = inv := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_2720]
  have hm13_1344 : MachineState.readWord M13 1344 = (n 0) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1344]
  have hm13_1376 : MachineState.readWord M13 1376 = (n 1) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1376]
  have hm13_1568 : MachineState.readWord M13 1568 = (n 7) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1568]
  have hm13_1600 : MachineState.readWord M13 1600 = (n 8) := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1600]
  have hm13_192 : MachineState.readWord M13 192 = Q2 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_192]
  have hm13_0 : MachineState.readWord M13 0 = Q3 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_0]
  have hm13_224 : MachineState.readWord M13 224 = Q4 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_224]
  have hm13_1216 : MachineState.readWord M13 1216 = Q5 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1216]
  have hm13_1248 : MachineState.readWord M13 1248 = Q6 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1248]
  have hm13_1088 : MachineState.readWord M13 1088 = Q1 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1088]
  have hm13_1280 : MachineState.readWord M13 1280 = Q7 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_1280]
  have hm13_800 : MachineState.readWord M13 800 = Z1 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_800]
  have hm13_832 : MachineState.readWord M13 832 = Z2 := by
    simp (disch := decide) only [M13, readWord_writeWord, read_disjoint, hm12_832]
  let M14 : ByteArray := MachineState.writeBytes (M13) (Data.Bytes.natToBytesPadded (Z4).toNat 32) 64
  have h13 : runInstructions R9InvCompactExec.stage13Program {s with pc := N 7389, memory := M13, stack := (C13) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7472, memory := M14, stack := (C14) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M14] using R9InvCompactContracts.stage13_history ({s with memory := M13}) (C13) (C14) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm13_768 hm13_32 hm13_64 hm13_96 hm13_128 hm13_160 hm13_2720 hm13_1344 hm13_1376 hm13_1568 hm13_1600 hm13_192 hm13_0 hm13_224 hm13_1216 hm13_1248 hm13_1088 hm13_1280 hm13_800 hm13_832 hq13 hc13
  have hm14_768 : MachineState.readWord M14 768 = Z0 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_768]
  have hm14_32 : MachineState.readWord M14 32 = Z3 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_32]
  have hm14_64 : MachineState.readWord M14 64 = Z4 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_64]
  have hm14_96 : MachineState.readWord M14 96 = ((a 5))+((a 5)) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_96]
  have hm14_128 : MachineState.readWord M14 128 = (a 6) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_128]
  have hm14_160 : MachineState.readWord M14 160 = (a 7) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_160]
  have hm14_2720 : MachineState.readWord M14 2720 = inv := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_2720]
  have hm14_1344 : MachineState.readWord M14 1344 = (n 0) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1344]
  have hm14_1376 : MachineState.readWord M14 1376 = (n 1) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1376]
  have hm14_1568 : MachineState.readWord M14 1568 = (n 7) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1568]
  have hm14_1600 : MachineState.readWord M14 1600 = (n 8) := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1600]
  have hm14_192 : MachineState.readWord M14 192 = Q2 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_192]
  have hm14_0 : MachineState.readWord M14 0 = Q3 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_0]
  have hm14_224 : MachineState.readWord M14 224 = Q4 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_224]
  have hm14_1216 : MachineState.readWord M14 1216 = Q5 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1216]
  have hm14_1248 : MachineState.readWord M14 1248 = Q6 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1248]
  have hm14_1088 : MachineState.readWord M14 1088 = Q1 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1088]
  have hm14_1280 : MachineState.readWord M14 1280 = Q7 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_1280]
  have hm14_800 : MachineState.readWord M14 800 = Z1 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_800]
  have hm14_832 : MachineState.readWord M14 832 = Z2 := by
    simp (disch := decide) only [M14, readWord_writeWord, read_disjoint, hm13_832]
  let M15 : ByteArray := MachineState.writeBytes (M14) (Data.Bytes.natToBytesPadded (Z5).toNat 32) 96
  have h14 : runInstructions R9InvCompactExec.stage14Program {s with pc := N 7472, memory := M14, stack := (C14) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Q5) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7551, memory := M15, stack := (C15) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M15] using R9InvCompactContracts.stage14_history ({s with memory := M14}) (C14) (C15) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm14_768 hm14_32 hm14_64 hm14_96 hm14_128 hm14_160 hm14_2720 hm14_1344 hm14_1376 hm14_1568 hm14_1600 hm14_192 hm14_0 hm14_224 hm14_1216 hm14_1248 hm14_1088 hm14_1280 hm14_800 hm14_832 hq14 hc14
  have hm15_768 : MachineState.readWord M15 768 = Z0 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_768]
  have hm15_32 : MachineState.readWord M15 32 = Z3 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_32]
  have hm15_64 : MachineState.readWord M15 64 = Z4 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_64]
  have hm15_96 : MachineState.readWord M15 96 = Z5 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_96]
  have hm15_128 : MachineState.readWord M15 128 = (a 6) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_128]
  have hm15_160 : MachineState.readWord M15 160 = (a 7) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_160]
  have hm15_2720 : MachineState.readWord M15 2720 = inv := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_2720]
  have hm15_1344 : MachineState.readWord M15 1344 = (n 0) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1344]
  have hm15_1376 : MachineState.readWord M15 1376 = (n 1) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1376]
  have hm15_1568 : MachineState.readWord M15 1568 = (n 7) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1568]
  have hm15_1600 : MachineState.readWord M15 1600 = (n 8) := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1600]
  have hm15_192 : MachineState.readWord M15 192 = Q2 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_192]
  have hm15_0 : MachineState.readWord M15 0 = Q3 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_0]
  have hm15_224 : MachineState.readWord M15 224 = Q4 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_224]
  have hm15_1216 : MachineState.readWord M15 1216 = Q5 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1216]
  have hm15_1248 : MachineState.readWord M15 1248 = Q6 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1248]
  have hm15_1088 : MachineState.readWord M15 1088 = Q1 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1088]
  have hm15_1280 : MachineState.readWord M15 1280 = Q7 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_1280]
  have hm15_800 : MachineState.readWord M15 800 = Z1 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_800]
  have hm15_832 : MachineState.readWord M15 832 = Z2 := by
    simp (disch := decide) only [M15, readWord_writeWord, read_disjoint, hm14_832]
  let M16 : ByteArray := MachineState.writeBytes (M15) (Data.Bytes.natToBytesPadded (Z6).toNat 32) 128
  have h15 : runInstructions R9InvCompactExec.stage15Program {s with pc := N 7551, memory := M15, stack := (C15) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Q6) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7607, memory := M16, stack := (C16) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M16] using R9InvCompactContracts.stage15_history ({s with memory := M15}) (C15) (C16) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm15_768 hm15_32 hm15_64 hm15_96 hm15_128 hm15_160 hm15_2720 hm15_1344 hm15_1376 hm15_1568 hm15_1600 hm15_192 hm15_0 hm15_224 hm15_1216 hm15_1248 hm15_1088 hm15_1280 hm15_800 hm15_832 hq15 hc15
  have hm16_768 : MachineState.readWord M16 768 = Z0 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_768]
  have hm16_32 : MachineState.readWord M16 32 = Z3 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_32]
  have hm16_64 : MachineState.readWord M16 64 = Z4 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_64]
  have hm16_96 : MachineState.readWord M16 96 = Z5 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_96]
  have hm16_128 : MachineState.readWord M16 128 = Z6 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_128]
  have hm16_160 : MachineState.readWord M16 160 = (a 7) := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_160]
  have hm16_2720 : MachineState.readWord M16 2720 = inv := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_2720]
  have hm16_1344 : MachineState.readWord M16 1344 = (n 0) := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1344]
  have hm16_1376 : MachineState.readWord M16 1376 = (n 1) := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1376]
  have hm16_1568 : MachineState.readWord M16 1568 = (n 7) := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1568]
  have hm16_1600 : MachineState.readWord M16 1600 = (n 8) := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1600]
  have hm16_192 : MachineState.readWord M16 192 = Q2 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_192]
  have hm16_0 : MachineState.readWord M16 0 = Q3 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_0]
  have hm16_224 : MachineState.readWord M16 224 = Q4 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_224]
  have hm16_1216 : MachineState.readWord M16 1216 = Q5 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1216]
  have hm16_1248 : MachineState.readWord M16 1248 = Q6 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1248]
  have hm16_1088 : MachineState.readWord M16 1088 = Q1 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1088]
  have hm16_1280 : MachineState.readWord M16 1280 = Q7 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_1280]
  have hm16_800 : MachineState.readWord M16 800 = Z1 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_800]
  have hm16_832 : MachineState.readWord M16 832 = Z2 := by
    simp (disch := decide) only [M16, readWord_writeWord, read_disjoint, hm15_832]
  let M17 : ByteArray := MachineState.writeBytes (M16) (Data.Bytes.natToBytesPadded (Z7).toNat 32) 160
  have h16 : runInstructions R9InvCompactExec.stage16Program {s with pc := N 7607, memory := M16, stack := (C16) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: (Q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7648, memory := M17, stack := (C17) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} := by
    simpa only [M17] using R9InvCompactContracts.stage16_history ({s with memory := M16}) (C16) (C17) (Q0) (Q1) (Q2) (Q3) (Q4) (Q5) (Q6) (Q7) (Q8) (Z0) (Z1) (Z2) (Z3) (Z4) (Z5) (Z6) (Z7) ((a 0)) ((a 1)) ((a 2)) ((a 3)) ((a 4)) ((a 5)) ((a 6)) ((a 7)) ((a 8)) ((n 0)) ((n 1)) ((n 2)) ((n 3)) ((n 4)) ((n 5)) ((n 6)) ((n 7)) ((n 8)) (p) (inv) rest hcap hact hm16_768 hm16_32 hm16_64 hm16_96 hm16_128 hm16_160 hm16_2720 hm16_1344 hm16_1376 hm16_1568 hm16_1600 hm16_192 hm16_0 hm16_224 hm16_1216 hm16_1248 hm16_1088 hm16_1280 hm16_800 hm16_832 hq16 hc16
  have hm17_768 : MachineState.readWord M17 768 = Z0 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_768]
  have hm17_32 : MachineState.readWord M17 32 = Z3 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_32]
  have hm17_64 : MachineState.readWord M17 64 = Z4 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_64]
  have hm17_96 : MachineState.readWord M17 96 = Z5 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_96]
  have hm17_128 : MachineState.readWord M17 128 = Z6 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_128]
  have hm17_160 : MachineState.readWord M17 160 = Z7 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_160]
  have hm17_2720 : MachineState.readWord M17 2720 = inv := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_2720]
  have hm17_1344 : MachineState.readWord M17 1344 = (n 0) := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1344]
  have hm17_1376 : MachineState.readWord M17 1376 = (n 1) := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1376]
  have hm17_1568 : MachineState.readWord M17 1568 = (n 7) := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1568]
  have hm17_1600 : MachineState.readWord M17 1600 = (n 8) := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1600]
  have hm17_192 : MachineState.readWord M17 192 = Q2 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_192]
  have hm17_0 : MachineState.readWord M17 0 = Q3 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_0]
  have hm17_224 : MachineState.readWord M17 224 = Q4 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_224]
  have hm17_1216 : MachineState.readWord M17 1216 = Q5 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1216]
  have hm17_1248 : MachineState.readWord M17 1248 = Q6 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1248]
  have hm17_1088 : MachineState.readWord M17 1088 = Q1 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1088]
  have hm17_1280 : MachineState.readWord M17 1280 = Q7 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_1280]
  have hm17_800 : MachineState.readWord M17 800 = Z1 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_800]
  have hm17_832 : MachineState.readWord M17 832 = Z2 := by
    simp (disch := decide) only [M17, readWord_writeWord, read_disjoint, hm16_832]
  have h17 : runInstructions R9InvCompactExec.stage17Program {s with pc := N 7648, memory := M17, stack := (C17) :: ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (Q8) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7657, memory := M17, stack := ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: ((n 0)) :: ((n 3)) :: (C17) :: rest} := by
    simpa only [R9InvCompactExec.stage17Model, hm17_1344] using R9InvCompactExec.stage17_run ({s with memory := M17}) (C17) ((n 2)) ((n 6)) ((n 4)) (Z1) (Z2) ((n 5)) ((n 7)) (p) ((n 8)) ((n 1)) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (Q8) ((n 3)) ((a 8)) rest hcap hact
  have hh : runInstructions program {s with pc := N 5568, memory := M0, stack := ((n 2)) :: ((n 6)) :: ((n 4)) :: ((a 1)) :: ((a 2)) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N (2^240-1)) :: ((n 0)) :: ((n 3)) :: ((a 8)) :: rest} = some {s with pc := N 7657, memory := M17, stack := ((n 2)) :: ((n 6)) :: ((n 4)) :: (Z1) :: (Z2) :: ((n 5)) :: ((n 7)) :: (p) :: ((n 8)) :: ((n 1)) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: ((n 0)) :: ((n 3)) :: (C17) :: rest} := (runInstructions_append_some _ _ _ _ _ h0 (runInstructions_append_some _ _ _ _ _ h1 (runInstructions_append_some _ _ _ _ _ h2 (runInstructions_append_some _ _ _ _ _ h3 (runInstructions_append_some _ _ _ _ _ h4 (runInstructions_append_some _ _ _ _ _ h5 (runInstructions_append_some _ _ _ _ _ h6 (runInstructions_append_some _ _ _ _ _ h7 (runInstructions_append_some _ _ _ _ _ h8 (runInstructions_append_some _ _ _ _ _ h9 (runInstructions_append_some _ _ _ _ _ h10 (runInstructions_append_some _ _ _ _ _ h11 (runInstructions_append_some _ _ _ _ _ h12 (runInstructions_append_some _ _ _ _ _ h13 (runInstructions_append_some _ _ _ _ _ h14 (runInstructions_append_some _ _ _ _ _ h15 (runInstructions_append_some _ _ _ _ _ h16 h17)))))))))))))))))
  have he : M17 = historyMemory s.memory inv a b n := by
    simpa only [M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15, M16, M17, newMemory] using memory_same s.memory inv a b n
  rw [he] at hh
  simpa only [M0, CycleSubmission.SquareMeaning.frame0, CycleSubmission.SquareMeaning.frame15, List.cons_append, List.nil_append, mask240_literal] using hh
#print axioms run
end R9InvCompactComplete

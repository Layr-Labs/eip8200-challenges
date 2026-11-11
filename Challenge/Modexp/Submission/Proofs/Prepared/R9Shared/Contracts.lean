import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Exec
import Challenge.Modexp.Submission.Proofs.Prepared.R9Shared.Edges
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace R9InvConsumeContracts
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Prepared.Arithmetic R5SharedTools Challenge.EvmProof.Memory
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "W" => UInt256
local notation "N" => UInt256.ofNat
theorem stage0_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = a0)
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (hq : R9SharedMath0.qNew a0 n0 p inv = q0) (hc : R9SharedMath0.cNew a0 n0 p inv = cn) :
    runInstructions R9InvConsumeExec.stage0Program {s with pc := N 5568, memory := s.memory, stack := (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N (2^240-1)) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 5631, memory := s.memory, stack := (cn) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((inv)*((a0)*(a0))) = q0 := by
    simpa only [R9SharedMath0.qNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (n0) (q0) (p))+(UInt256.mulMod (a0) (a0) (p))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath0.cNew] at hh
    rw [hq] at hh
    simpa only [mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage0Model s (n2) (n6) (n4) (a1) (a2) (n5) (n7) (p) (n8) (n1) (N (2^240-1)) (n0) (n3) (a8) rest = {s with pc := N 5631, memory := s.memory, stack := (cn) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage0Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage0_run s (n2) (n6) (n4) (a1) (a2) (n5) (n7) (p) (n8) (n1) (N (2^240-1)) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage1_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = a0)
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (hq : R9SharedMath1.qNew c q0 a0 a1 n0 n1 p inv = q1) (hc : R9SharedMath1.cNew c q0 a0 a1 n0 n1 p inv = cn) :
    runInstructions R9InvConsumeExec.stage1Program {s with pc := N 5631, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 5709, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a0)+(a0)).toNat 32) 768, stack := (cn) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((n1)*(q0))+((c)+((a1)*((a0)+(a0)))))*(inv)) = q1 := by
    simpa only [R9SharedMath1.qNew, R9SharedMath1.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q1) (n0) (p))+((UInt256.mulMod (q0) (n1) (p))+((c)+(UInt256.mulMod (a1) ((a0)+(a0)) (p))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath1.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath1.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage1Model s (c) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 5709, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a0)+(a0)).toNat 32) 768, stack := (cn) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage1Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage1_run s (c) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage2_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (hq : R9SharedMath2.qNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = q2) (hc : R9SharedMath2.cNew c q0 q1 a0 a1 a2 n0 n1 n2 p inv = cn) :
    runInstructions R9InvConsumeExec.stage2Program {s with pc := N 5709, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (a1) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 5802, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q2).toNat 32) 192, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((n1)*(q1))+((((c)+((a2)*((a0)+(a0))))+((a1)*(a1)))+((q0)*(n2))))*(inv)) = q2 := by
    simpa only [R9SharedMath2.qNew, R9SharedMath2.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q2) (n0) (p))+((UInt256.mulMod (q1) (n1) (p))+((UInt256.mulMod (q0) (n2) (p))+((UInt256.mulMod (a1) (a1) (p))+((c)+(UInt256.mulMod (a2) ((a0)+(a0)) (p))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath2.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath2.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage2Model s (c) (n2) (n6) (n4) (a1) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 5802, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q2).toNat 32) 192, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage2Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage2_run s (c) (n2) (n6) (n4) (a1) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage3_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (hq : R9SharedMath3.qNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = q3) (hc : R9SharedMath3.cNew c q0 q1 q2 a0 a1 a2 a3 n0 n1 n2 n3 p inv = cn) :
    runInstructions R9InvConsumeExec.stage3Program {s with pc := N 5802, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 5907, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q3).toNat 32) 0, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((q2)*(n1))+(((q1)*(n2))+(((q0)*(n3))+((c)+((((a1)+(a1))*(a2))+((a3)*((a0)+(a0))))))))*(inv)) = q3 := by
    simpa only [R9SharedMath3.qNew, R9SharedMath3.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q3) (n0) (p))+((UInt256.mulMod (q2) (n1) (p))+((UInt256.mulMod (q1) (n2) (p))+((UInt256.mulMod (q0) (n3) (p))+((c)+((UInt256.mulMod ((a1)+(a1)) (a2) (p))+(UInt256.mulMod (a3) ((a0)+(a0)) (p)))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath3.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath3.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage3Model s (c) (n2) (n6) (n4) ((a1)+(a1)) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 5907, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q3).toNat 32) 0, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage3Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage3_run s (c) (n2) (n6) (n4) ((a1)+(a1)) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage4_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (hq : R9SharedMath4.qNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = q4) (hc : R9SharedMath4.cNew c q0 q1 q2 q3 a0 a1 a2 a3 a4 n0 n1 n2 n3 n4 p inv = cn) :
    runInstructions R9InvConsumeExec.stage4Program {s with pc := N 5907, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: (a2) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 6040, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q4).toNat 32) 224, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((q3)*(n1))+(((q2)*(n2))+(((q1)*(n3))+(((q0)*(n4))+(((a2)*(a2))+((c)+((((a1)+(a1))*(a3))+((a4)*((a0)+(a0))))))))))*(inv)) = q4 := by
    simpa only [R9SharedMath4.qNew, R9SharedMath4.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q4) (n0) (p))+((UInt256.mulMod (q3) (n1) (p))+((UInt256.mulMod (q2) (n2) (p))+((UInt256.mulMod (q1) (n3) (p))+((UInt256.mulMod (q0) (n4) (p))+((UInt256.mulMod (a2) (a2) (p))+((c)+((UInt256.mulMod ((a1)+(a1)) (a3) (p))+(UInt256.mulMod (a4) ((a0)+(a0)) (p)))))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath4.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath4.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage4Model s (c) (n2) (n6) (n4) ((a1)+(a1)) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 6040, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q4).toNat 32) 224, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage4Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage4_run s (c) (n2) (n6) (n4) ((a1)+(a1)) (a2) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage5_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (hq : R9SharedMath5.qNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv = q5) (hc : R9SharedMath5.cNew c q0 q1 q2 q3 q4 a0 a1 a2 a3 a4 a5 n0 n1 n2 n3 n4 n5 p inv = cn) :
    runInstructions R9InvConsumeExec.stage5Program {s with pc := N 6040, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 6188, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q5).toNat 32) 1216, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((q4)*(n1))+(((q3)*(n2))+(((q2)*(n3))+(((q1)*(n4))+(((q0)*(n5))+((c)+((((a2)+(a2))*(a3))+((((a1)+(a1))*(a4))+((a5)*((a0)+(a0)))))))))))*(inv)) = q5 := by
    simpa only [R9SharedMath5.qNew, R9SharedMath5.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q5) (n0) (p))+((UInt256.mulMod (q4) (n1) (p))+((UInt256.mulMod (q3) (n2) (p))+((UInt256.mulMod (q2) (n3) (p))+((UInt256.mulMod (q1) (n4) (p))+((UInt256.mulMod (q0) (n5) (p))+((c)+((UInt256.mulMod ((a2)+(a2)) (a3) (p))+((UInt256.mulMod ((a1)+(a1)) (a4) (p))+(UInt256.mulMod (a5) ((a0)+(a0)) (p))))))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath5.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath5.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage5Model s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 6188, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q5).toNat 32) 1216, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage5Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage5_run s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage6_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = a3)
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (hq : R9SharedMath6.qNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv = q6) (hc : R9SharedMath6.cNew c q0 q1 q2 q3 q4 q5 a0 a1 a2 a3 a4 a5 a6 n0 n1 n2 n3 n4 n5 n6 p inv = cn) :
    runInstructions R9InvConsumeExec.stage6Program {s with pc := N 6188, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 6370, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a3)+(a3)).toNat 32) 32) (Data.Bytes.natToBytesPadded (q6).toNat 32) 1248, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((q5)*(n1))+(((q4)*(n2))+(((q3)*(n3))+(((q2)*(n4))+(((q1)*(n5))+(((q0)*(n6))+(((a3)*(a3))+((c)+((((a2)+(a2))*(a4))+((((a1)+(a1))*(a5))+((a6)*((a0)+(a0)))))))))))))*(inv)) = q6 := by
    simpa only [R9SharedMath6.qNew, R9SharedMath6.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q6) (n0) (p))+((UInt256.mulMod (q5) (n1) (p))+((UInt256.mulMod (q4) (n2) (p))+((UInt256.mulMod (q3) (n3) (p))+((UInt256.mulMod (q2) (n4) (p))+((UInt256.mulMod (q1) (n5) (p))+((UInt256.mulMod (q0) (n6) (p))+((UInt256.mulMod (a3) (a3) (p))+((c)+((UInt256.mulMod ((a2)+(a2)) (a4) (p))+((UInt256.mulMod ((a1)+(a1)) (a5) (p))+(UInt256.mulMod (a6) ((a0)+(a0)) (p))))))))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath6.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath6.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage6Model s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 6370, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a3)+(a3)).toNat 32) 32) (Data.Bytes.natToBytesPadded (q6).toNat 32) 1248, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage6Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage6_run s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage7_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (hq : R9SharedMath7.qNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv = q7) (hc : R9SharedMath7.cNew c q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 p inv = cn) :
    runInstructions R9InvConsumeExec.stage7Program {s with pc := N 6370, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (q1) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 6575, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q1).toNat 32) 1088) (Data.Bytes.natToBytesPadded (q7).toNat 32) 1280, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) ((((q6)*(n1))+(((q5)*(n2))+(((q4)*(n3))+(((q3)*(n4))+(((q2)*(n5))+(((q1)*(n6))+(((n7)*(q0))+((c)+((((a3)+(a3))*(a4))+((((a2)+(a2))*(a5))+(((a6)*((a1)+(a1)))+((a7)*((a0)+(a0))))))))))))))*(inv)) = q7 := by
    simpa only [R9SharedMath7.qNew, R9SharedMath7.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (q7) (n0) (p))+((UInt256.mulMod (q6) (n1) (p))+((UInt256.mulMod (q5) (n2) (p))+((UInt256.mulMod (q4) (n3) (p))+((UInt256.mulMod (q3) (n4) (p))+((UInt256.mulMod (q2) (n5) (p))+((UInt256.mulMod (q1) (n6) (p))+((UInt256.mulMod (n7) (q0) (p))+((c)+((UInt256.mulMod ((a3)+(a3)) (a4) (p))+((UInt256.mulMod ((a2)+(a2)) (a5) (p))+((UInt256.mulMod ((a1)+(a1)) (a6) (p))+(UInt256.mulMod (a7) ((a0)+(a0)) (p)))))))))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath7.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath7.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage7Model s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 6575, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (q1).toNat 32) 1088) (Data.Bytes.natToBytesPadded (q7).toNat 32) 1280, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage7Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage7_run s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (q1) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage8_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = a4)
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (hq : R9SharedMath8.qNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv = q8) (hc : R9SharedMath8.cNew c q0 q1 q2 q3 q4 q5 q6 q7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv = cn) :
    runInstructions R9InvConsumeExec.stage8Program {s with pc := N 6575, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (q0) :: (n1) :: (inv) :: (n0) :: (n3) :: (a8) :: rest} = some {s with pc := N 6813, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a4)+(a4)).toNat 32) 64, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land ((inv)*(((q7)*(n1))+(((q6)*(n2))+(((q5)*(n3))+(((q4)*(n4))+(((q3)*(n5))+(((q2)*(n6))+(((n7)*(q1))+(((n8)*(q0))+(((a4)*(a4))+((c)+((((a3)+(a3))*(a5))+((((a2)+(a2))*(a6))+(((a7)*((a1)+(a1)))+((a8)*((a0)+(a0))))))))))))))))) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) = q8 := by
    simpa only [R9SharedMath8.qNew, R9SharedMath8.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((UInt256.mulMod (n0) (q8) (p))+((UInt256.mulMod (q7) (n1) (p))+((UInt256.mulMod (q6) (n2) (p))+((UInt256.mulMod (q5) (n3) (p))+((UInt256.mulMod (q4) (n4) (p))+((UInt256.mulMod (q3) (n5) (p))+((UInt256.mulMod (q2) (n6) (p))+((UInt256.mulMod (n7) (q1) (p))+((UInt256.mulMod (a4) (a4) (p))+((UInt256.mulMod (n8) (q0) (p))+((c)+((UInt256.mulMod ((a3)+(a3)) (a5) (p))+((UInt256.mulMod ((a2)+(a2)) (a6) (p))+((UInt256.mulMod ((a1)+(a1)) (a7) (p))+(UInt256.mulMod (a8) ((a0)+(a0)) (p)))))))))))))))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath8.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath8.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage8Model s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (n7) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest = {s with pc := N 6813, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a4)+(a4)).toNat 32) 64, stack := (cn) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage8Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage8_run s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (n7) (p) (q0) (n1) (inv) (n0) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage9_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = (a0)+(a0))
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = (a4)+(a4))
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (hq : R9SharedMath9.qNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p = z0) (hc : R9SharedMath9.cNew c q1 q2 q3 q4 q5 q6 q7 q8 a1 a2 a3 a4 a5 a6 a7 a8 n1 n2 n3 n4 n5 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage9Program {s with pc := N 6813, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: ((a1)+(a1)) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 6994, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z0).toNat 32) 768, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n1))+(((q7)*(n2))+(((q6)*(n3))+(((q5)*(n4))+(((q4)*(n5))+(((q3)*(n6))+(((n7)*(q2))+(((n8)*(q1))+((c)+((((a4)+(a4))*(a5))+((((a3)+(a3))*(a6))+((((a2)+(a2))*(a7))+((a8)*((a1)+(a1))))))))))))))) = z0 := by
    simpa only [R9SharedMath9.qNew, R9SharedMath9.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (q8) (n1) (p))+((UInt256.mulMod (q7) (n2) (p))+((UInt256.mulMod (q6) (n3) (p))+((UInt256.mulMod (q5) (n4) (p))+((UInt256.mulMod (q4) (n5) (p))+((UInt256.mulMod (q3) (n6) (p))+((UInt256.mulMod (n7) (q2) (p))+((UInt256.mulMod (n8) (q1) (p))+((c)+((UInt256.mulMod ((a4)+(a4)) (a5) (p))+((UInt256.mulMod ((a3)+(a3)) (a6) (p))+((UInt256.mulMod ((a2)+(a2)) (a7) (p))+(UInt256.mulMod (a8) ((a1)+(a1)) (p))))))))))))))-(z0))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath9.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath9.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage9Model s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (n7) (p) (n8) (n1) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 6994, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z0).toNat 32) 768, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage9Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage9_run s (c) (n2) (n6) (n4) ((a1)+(a1)) ((a2)+(a2)) (n5) (n7) (p) (n8) (n1) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage10_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = (a4)+(a4))
    (h96 : MachineState.readWord s.memory 96 = a5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (hq : R9SharedMath10.qNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p = z1) (hc : R9SharedMath10.cNew c q2 q3 q4 q5 q6 q7 q8 a2 a3 a4 a5 a6 a7 a8 n2 n3 n4 n5 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage10Program {s with pc := N 6994, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: ((a2)+(a2)) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7160, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a5)+(a5)).toNat 32) 96) (Data.Bytes.natToBytesPadded (z1).toNat 32) 800, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n2))+(((n3)*(q7))+(((q6)*(n4))+(((q5)*(n5))+(((q4)*(n6))+(((n7)*(q3))+(((n8)*(q2))+(((a5)*(a5))+((c)+((((a4)+(a4))*(a6))+((((a3)+(a3))*(a7))+((a8)*((a2)+(a2)))))))))))))) = z1 := by
    simpa only [R9SharedMath10.qNew, R9SharedMath10.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (q8) (n2) (p))+((UInt256.mulMod (q7) (n3) (p))+((UInt256.mulMod (q6) (n4) (p))+((UInt256.mulMod (q5) (n5) (p))+((UInt256.mulMod (q4) (n6) (p))+((UInt256.mulMod (n7) (q3) (p))+((UInt256.mulMod (n8) (q2) (p))+((UInt256.mulMod (a5) (a5) (p))+((c)+((UInt256.mulMod ((a4)+(a4)) (a6) (p))+((UInt256.mulMod ((a3)+(a3)) (a7) (p))+(UInt256.mulMod (a8) ((a2)+(a2)) (p)))))))))))))-(z1))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath10.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath10.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage10Model s (c) (n2) (n6) (n4) (q6) ((a2)+(a2)) (n5) (n7) (p) (n8) (n1) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7160, memory := MachineState.writeBytes (MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded ((a5)+(a5)).toNat 32) 96) (Data.Bytes.natToBytesPadded (z1).toNat 32) 800, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage10Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage10_run s (c) (n2) (n6) (n4) (q6) ((a2)+(a2)) (n5) (n7) (p) (n8) (n1) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage11_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = (a4)+(a4))
    (h96 : MachineState.readWord s.memory 96 = (a5)+(a5))
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (hq : R9SharedMath11.qNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p = z2) (hc : R9SharedMath11.cNew c q3 q4 q5 q6 q7 q8 a3 a4 a5 a6 a7 a8 n3 n4 n5 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage11Program {s with pc := N 7160, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7280, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z2).toNat 32) 832, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n3))+(((n4)*(q7))+(((q6)*(n5))+(((q5)*(n6))+(((n7)*(q4))+(((n8)*(q3))+((((a6)*((a5)+(a5)))+(((a7)*((a4)+(a4)))+((a8)*((a3)+(a3)))))+(c)))))))) = z2 := by
    simpa only [R9SharedMath11.qNew, R9SharedMath11.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (q8) (n3) (p))+((UInt256.mulMod (q7) (n4) (p))+((UInt256.mulMod (q6) (n5) (p))+((UInt256.mulMod (q5) (n6) (p))+((UInt256.mulMod (n7) (q4) (p))+((UInt256.mulMod (n8) (q3) (p))+((c)+((UInt256.mulMod (a6) ((a5)+(a5)) (p))+((UInt256.mulMod (a7) ((a4)+(a4)) (p))+(UInt256.mulMod ((a3)+(a3)) (a8) (p)))))))))))-(z2))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath11.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath11.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage11Model s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7280, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z2).toNat 32) 832, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage11Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage11_run s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage12_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = (a3)+(a3))
    (h64 : MachineState.readWord s.memory 64 = (a4)+(a4))
    (h96 : MachineState.readWord s.memory 96 = (a5)+(a5))
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (h832 : MachineState.readWord s.memory 832 = z2)
    (hq : R9SharedMath12.qNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p = z3) (hc : R9SharedMath12.cNew c q4 q5 q6 q7 q8 a4 a5 a6 a7 a8 n4 n5 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage12Program {s with pc := N 7280, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7387, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z3).toNat 32) 32, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n4))+(((n5)*(q7))+(((q6)*(n6))+(((n7)*(q5))+(((n8)*(q4))+(((a6)*(a6))+((((a7)*((a5)+(a5)))+((a8)*((a4)+(a4))))+(c)))))))) = z3 := by
    simpa only [R9SharedMath12.qNew, R9SharedMath12.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (q8) (n4) (p))+((UInt256.mulMod (n5) (q7) (p))+((UInt256.mulMod (q6) (n6) (p))+((UInt256.mulMod (n7) (q5) (p))+((UInt256.mulMod (n8) (q4) (p))+((UInt256.mulMod (a6) (a6) (p))+((c)+((UInt256.mulMod (a7) ((a5)+(a5)) (p))+(UInt256.mulMod ((a4)+(a4)) (a8) (p))))))))))-(z3))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath12.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath12.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage12Model s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7387, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z3).toNat 32) 32, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage12Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, h832, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage12_run s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage13_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = z3)
    (h64 : MachineState.readWord s.memory 64 = (a4)+(a4))
    (h96 : MachineState.readWord s.memory 96 = (a5)+(a5))
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (h832 : MachineState.readWord s.memory 832 = z2)
    (hq : R9SharedMath13.qNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p = z4) (hc : R9SharedMath13.cNew c q5 q6 q7 q8 a5 a6 a7 a8 n5 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage13Program {s with pc := N 7387, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7470, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z4).toNat 32) 64, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n5))+(((n6)*(q7))+(((n7)*(q6))+(((n8)*(q5))+((((a7)*((a6)+(a6)))+((a8)*((a5)+(a5))))+(c)))))) = z4 := by
    simpa only [R9SharedMath13.qNew, R9SharedMath13.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (q8) (n5) (p))+((UInt256.mulMod (q7) (n6) (p))+((UInt256.mulMod (n7) (q6) (p))+((UInt256.mulMod (n8) (q5) (p))+((c)+((UInt256.mulMod (a7) ((a6)+(a6)) (p))+(UInt256.mulMod ((a5)+(a5)) (a8) (p))))))))-(z4))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath13.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath13.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage13Model s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7470, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z4).toNat 32) 64, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage13Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, h832, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage13_run s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage14_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = z3)
    (h64 : MachineState.readWord s.memory 64 = z4)
    (h96 : MachineState.readWord s.memory 96 = (a5)+(a5))
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (h832 : MachineState.readWord s.memory 832 = z2)
    (hq : R9SharedMath14.qNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p = z5) (hc : R9SharedMath14.cNew c q6 q7 q8 a6 a7 a8 n6 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage14Program {s with pc := N 7470, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: (q5) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7549, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z5).toNat 32) 96, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n6))+(((n7)*(q7))+(((n8)*(q6))+(((a7)*(a7))+((c)+((a8)*((a6)+(a6)))))))) = z5 := by
    simpa only [R9SharedMath14.qNew, R9SharedMath14.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (n6) (q8) (p))+((UInt256.mulMod (n7) (q7) (p))+((UInt256.mulMod (n8) (q6) (p))+((UInt256.mulMod (a7) (a7) (p))+((c)+(UInt256.mulMod (a8) ((a6)+(a6)) (p)))))))-(z5))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath14.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath14.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage14Model s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7549, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z5).toNat 32) 96, stack := (cn) :: (n2) :: (n6) :: (n4) :: (q6) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage14Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, h832, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage14_run s (c) (n2) (n6) (n4) (q6) (q5) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage15_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = z3)
    (h64 : MachineState.readWord s.memory 64 = z4)
    (h96 : MachineState.readWord s.memory 96 = z5)
    (h128 : MachineState.readWord s.memory 128 = a6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (h832 : MachineState.readWord s.memory 832 = z2)
    (hq : R9SharedMath15.qNew c q7 q8 a7 a8 n7 n8 p = z6) (hc : R9SharedMath15.cNew c q7 q8 a7 a8 n7 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage15Program {s with pc := N 7549, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (q6) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7605, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z6).toNat 32) 128, stack := (cn) :: (n2) :: (n6) :: (n4) :: (z1) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((q8)*(n7))+(((q7)*(n8))+((c)+((a8)*((a7)+(a7)))))) = z6 := by
    simpa only [R9SharedMath15.qNew, R9SharedMath15.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+(((UInt256.mulMod (n7) (q8) (p))+((UInt256.mulMod (q7) (n8) (p))+((c)+(UInt256.mulMod (a8) ((a7)+(a7)) (p)))))-(z6))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath15.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath15.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage15Model s (c) (n2) (n6) (n4) (q6) (z2) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7605, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z6).toNat 32) 128, stack := (cn) :: (n2) :: (n6) :: (n4) :: (z1) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage15Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, h832, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage15_run s (c) (n2) (n6) (n4) (q6) (z2) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
theorem stage16_history (s : State) (c cn q0 q1 q2 q3 q4 q5 q6 q7 q8 z0 z1 z2 z3 z4 z5 z6 z7 a0 a1 a2 a3 a4 a5 a6 a7 a8 n0 n1 n2 n3 n4 n5 n6 n7 n8 p inv : W) (rest : List W)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (h768 : MachineState.readWord s.memory 768 = z0)
    (h32 : MachineState.readWord s.memory 32 = z3)
    (h64 : MachineState.readWord s.memory 64 = z4)
    (h96 : MachineState.readWord s.memory 96 = z5)
    (h128 : MachineState.readWord s.memory 128 = z6)
    (h160 : MachineState.readWord s.memory 160 = a7)
    (h2720 : MachineState.readWord s.memory 2720 = inv)
    (h1344 : MachineState.readWord s.memory 1344 = n0)
    (h1376 : MachineState.readWord s.memory 1376 = n1)
    (h1568 : MachineState.readWord s.memory 1568 = n7)
    (h1600 : MachineState.readWord s.memory 1600 = n8)
    (h192 : MachineState.readWord s.memory 192 = q2)
    (h0 : MachineState.readWord s.memory 0 = q3)
    (h224 : MachineState.readWord s.memory 224 = q4)
    (h1216 : MachineState.readWord s.memory 1216 = q5)
    (h1248 : MachineState.readWord s.memory 1248 = q6)
    (h1088 : MachineState.readWord s.memory 1088 = q1)
    (h1280 : MachineState.readWord s.memory 1280 = q7)
    (h800 : MachineState.readWord s.memory 800 = z1)
    (h832 : MachineState.readWord s.memory 832 = z2)
    (hq : R9SharedMath16.qNew c q8 a8 n8 p = z7) (hc : R9SharedMath16.cNew c q8 a8 n8 p = cn) :
    runInstructions R9InvConsumeExec.stage16Program {s with pc := N 7605, memory := s.memory, stack := (c) :: (n2) :: (n6) :: (n4) :: (z1) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (q7) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} = some {s with pc := N 7646, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z7).toNat 32) 160, stack := (cn) :: (n2) :: (n6) :: (n4) :: (z1) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
  have hqr : UInt256.land (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (((c)+((a8)*(a8)))+((q8)*(n8))) = z7 := by
    simpa only [R9SharedMath16.qNew, R9SharedMath16.loNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hq
  have hcr : UInt256.mulMod (N 2048) ((p)+((((c)+(UInt256.mulMod (a8) (a8) (p)))+(UInt256.mulMod (q8) (n8) (p)))-(z7))) (p) = cn := by
    have hh := hc
    simp only [R9SharedMath16.cNew] at hh
    rw [hq] at hh
    simpa only [R9SharedMath16.hiNew, mask240_literal, List.foldr_cons, List.foldr_nil, word_add0, addA, addL, addC, mulC, mmC, andC] using hh
  simp only [addA, addL, addC, mulC, mmC, andC] at hqr hcr
  have he : R9InvConsumeExec.stage16Model s (c) (n2) (n6) (n4) (z1) (z2) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest = {s with pc := N 7646, memory := MachineState.writeBytes (s.memory) (Data.Bytes.natToBytesPadded (z7).toNat 32) 160, stack := (cn) :: (n2) :: (n6) :: (n4) :: (z1) :: (z2) :: (n5) :: (n7) :: (p) :: (n8) :: (n1) :: (N 1766847064778384329583297500742918515827483896875618958121606201292619775) :: (q8) :: (n3) :: (a8) :: rest} := by
    simp (disch := decide) only [R9InvConsumeExec.stage16Model, readWord_writeWord, read_disjoint, h768, h32, h64, h96, h128, h160, h2720, h1344, h1376, h1568, h1600, h192, h0, h224, h1216, h1248, h1088, h1280, h800, h832, addA, addL, addC, mulC, mmC, andC, mask240_literal, hqr, hcr]
  have hh := R9InvConsumeExec.stage16_run s (c) (n2) (n6) (n4) (z1) (z2) (n5) (n7) (p) (n8) (q7) (N 1766847064778384329583297500742918515827483896875618958121606201292619775) (q8) (n3) (a8) rest hcap hact
  exact hh.trans (congrArg some he)
end R9InvConsumeContracts

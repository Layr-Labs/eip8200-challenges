import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1Last

set_option warningAsError true

/-! Last L1 memory/carry advance normally; its two old pointers remain until POPs. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1LastRun

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def program : List Instr :=
  (CiosCachedL1.loadProgram ++ CiosCachedMacCore.program) ++ CiosCachedL1Last.lastTail

def outputState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (ptrAt (pa + 32*n - 32) j),
      UInt256.ofNat (ptrAt (8224 + 32*n) j),
      (l1Step mem bi pa n (j+1)).carry, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l1Step mem bi pa n (j+1)).memory }

theorem run_tail (template : State) (pc pa pt sum carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pt.toNat 32) = template.activeWords) :
    runInstructions CiosCachedL1Last.lastTail
      (framed template pc
        ([sum, pa, pt, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) pt.toNat }
      (advancePC 2 pc)
      ([pa, pt, carry, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [runInstructions, CiosCachedL1Last.lastTail, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc13, hc14, State.activeWordsAfterUInt256, hactive]

theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions program (CiosCachedL1.state template pc mem bi pa n j pbi paEnd pbEnd flag destination returnPC rest) =
    some (outputState template (pc + UInt256.ofNat 32) mem bi pa n j
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hc11 : rest.length + 12 < 1024 := by omega
  have hc12 : rest.length + 13 < 1024 := by omega
  have hc13 : rest.length + 14 < 1024 := by omega
  have hc14 : rest.length + 15 < 1024 := by omega
  have hc15 : rest.length + 16 < 1024 := by omega
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    (by decide)
  have hN : allOnes = maxWord := allOnes_value
  have hsize : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  have hpaj : ptrAt (pa + 32*n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32*(n-1-j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8224 + 32*n) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32*(n-1-j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (pa + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive

  let st : State := { template with memory := (l1Step mem bi pa n j).memory }
  let pa0 := UInt256.ofNat (ptrAt (pa + 32*n - 32) j)
  let pt0 := UInt256.ofNat (ptrAt (8224 + 32*n) j)
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat pa0.toNat 32) =
      st.activeWords := by
    simpa only [st, pa0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpaj] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat pt0.toNat 32) =
      st.activeWords := by
    simpa only [st, pt0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hptj] using hactT
  have hl := CiosCachedL1.run_load st pc pa0 pt0 (l1Step mem bi pa n j).carry bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hA
  have hm := CiosCachedMacCore.run_mac st (advancePC 3 pc)
    (MachineState.readWord st.memory pa0.toNat) bi (l1Step mem bi pa n j).carry pa0 pt0
    ([pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have ht := run_tail st (advancePC 9 (advancePC 18 (advancePC 3 pc))) pa0 pt0
    (macSum (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory pt0.toNat) (l1Step mem bi pa n j).carry)
    (macCarry (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory pt0.toNat) (l1Step mem bi pa n j).carry)
    bi pbi paEnd pbEnd flag destination returnPC rest hrest hT
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both ht
  have hpc : advancePC 2 (advancePC 9 (advancePC 18 (advancePC 3 pc))) =
      pc + UInt256.ofNat 32 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program, st, pa0, pt0, CiosCachedL1.state, outputState, framed, l1Step,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpaj, hptj, hpc,
    Challenge.EvmProof.Word.ofNat_add_mod] using hall

/-- For n=2, the second L1 copy is the final one; no finite-width restriction. -/
theorem run_n2 (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*2 ≤ 9472) :
    runInstructions program (CiosCachedL1.state template pc mem bi pa 2 1
      pbi paEnd pbEnd flag destination returnPC rest) =
    some (outputState template (pc + UInt256.ofNat 32) mem bi pa 2 1
      pbi paEnd pbEnd flag destination returnPC rest) :=
  run_step template pc mem bi pa 2 1 pbi paEnd pbEnd flag destination returnPC rest
    hrest hactive (by decide) (by decide) hpa hpaFit

theorem program_matches : program = CiosCached.l1LastProgram := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1LastRun

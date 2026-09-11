import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMac
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandSnapshot

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def loadProgram (off : UInt256) : List Instr :=
  [.op .JUMPDEST, .push 2 (UInt256.ofNat 2400 + off), .op .MLOAD, .op (.Dup ⟨8, by decide⟩)]

def l1Program (off t : UInt256) : List Instr :=
  loadProgram off ++ macFusedProgram t t

theorem run_load (template : State)
    (pc off carry bi pbi paBase pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat 2400 + off).toNat 32) = template.activeWords) :
    runInstructions (loadProgram off)
      (framed template pc
        ([carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 6)
      ([maxWord, MachineState.readWord template.memory (UInt256.ofNat 2400 + off).toNat,
        carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by decide,
    Nat.reduceMod] at hactive
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, State.activeWordsAfterUInt256, hactive, allOnes_value,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 91 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hj : j < n)
    (_hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2048) (hsnapshot : Snapshot mem pa n) :
    runInstructions (l1Program off t)
      (CiosCachedL1.state template pc mem bi pa n j pbi pbEnd flag destination returnPC rest) =
    some (CiosCachedL1.state template (pc + UInt256.ofNat 38) mem bi pa n (j+1)
      pbi pbEnd flag destination returnPC rest) := by
  have haddr : (UInt256.ofNat pa + off).toNat = pa + 32*(n-1-j) := by
    rw [CiosCachedL1.base_offset_toNat pa off (by omega), hoff]
  have hsaddr : (UInt256.ofNat 2400 + off).toNat = 2400 + 32*(n-1-j) := by
    rw [CiosCachedL1.base_offset_toNat 2400 off (by omega), hoff]
  have hsread : MachineState.readWord (l1Step mem bi pa n j).memory
      (UInt256.ofNat 2400 + off).toNat =
      MachineState.readWord (l1Step mem bi pa n j).memory (UInt256.ofNat pa + off).toNat := by
    rw [hsaddr, haddr]
    exact (hsnapshot.l1 bi j hn hpaFit) (n-1-j) (by omega)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2400 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l1Step mem bi pa n j).memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat 2400 + off).toNat 32) = st.activeWords := by
    simpa only [st, hsaddr] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_load st pc off (l1Step mem bi pa n j).carry bi pbi (UInt256.ofNat pa)
    pbEnd flag destination returnPC rest hrest hA
  rw [show MachineState.readWord st.memory (UInt256.ofNat 2400 + off).toNat =
    MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat from hsread] at hl
  have hf := CiosCachedFused.run_fused st (pc + UInt256.ofNat 6)
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (l1Step mem bi pa n j).carry t t
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat 6) + UInt256.ofNat 32 =
      pc + UInt256.ofNat 38 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [l1Program, st, CiosCachedL1.state, framed, l1Step, haddr, ht, hpc,
    List.cons_append, List.nil_append] using hall


theorem run_l1Mac (pc : Nat) (off t : UInt256) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 91 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 8) (hj : j < n) (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 2112 + 32 * (n - 1 - j))
    (hpa : 32 ≤ pa) (hpaFit : pa + 32*n ≤ 2048) (hsnapshot : Snapshot mem pa n) :
    runInstructions (l1Program off t) (l1At pc s mem bi pa pb n i j pdst ret rest) =
      some (l1At (pc+38) s mem bi pa pb n i (j+1) pdst ret rest) := by
  have h := run_step s (UInt256.ofNat pc) mem bi pa n j off t hoff ht
    (UInt256.ofNat (ptrAt (pb+32*n-32) i))
    (UInt256.ofNat (pb-32)) (l1Target n) (l2Target n) pdst (ret :: rest) (by simp only [List.length_cons]; omega) hact hn32 hj hpa hpaFit hsnapshot
  simpa only [List.cons_append, List.nil_append, CiosCachedL1.state, l1At,
    Challenge.EvmProof.Word.ofNat_add_mod] using h


end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFixedL2Last
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailStore

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Located fixed-address terminal L2 cell

The bytecode replacement differs from the former terminal cell before its
pointer words are discarded.  This module therefore exposes the first common
full-state boundary: after the final cell and the first five row-tail
instructions, at pc 5267.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFixedL2LastRun

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast
open CiosCached CiosCachedMacCore CiosCachedTailDefs

private def prefixProgram : List Instr :=
  CiosCachedL2.loadProgram ++ CiosCachedMacCore.program

private def cleanupAfterDiscard : List Instr :=
  (CiosCached.tailProgram.drop 2).take 3

private theorem runProgram_eq (ops : List Instr) (s : State) :
    CiosCachedFixedL2Last.runProgram ops s = runInstructions ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change (Challenge.EvmProof.Stepper.runInstr op s).bind
          (CiosCachedFixedL2Last.runProgram ops) =
        (Challenge.EvmProof.Stepper.runInstr op s).bind (runInstructions ops)
      cases Challenge.EvmProof.Stepper.runInstr op s with
      | none => rfl
      | some next => exact ih next

private theorem l2LastProgram_eq :
    CiosCached.l2LastProgram = prefixProgram ++ CiosCachedFixedL2Last.fixedTail := by
  rfl

private theorem l2Program0_eq :
    CiosCached.l2Program 0 = prefixProgram ++ CiosCachedFixedL2Last.oldTail := by
  rfl

private theorem cleanupProgram_eq :
    CiosCachedTailDefs.cleanupProgram =
      CiosCachedFixedL2Last.discardPointers ++ cleanupAfterDiscard := by
  rfl

/-- Replacing the terminal cell preserves the complete state at the first
common cleanup boundary.  The final-copy equation is essential: it identifies
the old parameterized cell with its `p = 0`, fixed-address instance. -/
theorem run_final_cleanup (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hlast : k + 2 = n) :
    runInstructions (CiosCached.l2LastProgram ++ CiosCachedTailDefs.cleanupProgram)
      (CiosCached.l2At 5222 s mem bi mu c0 pa pb n i k pdst ret rest) =
    some (CiosCachedTailDefs.cleaned
      { s with memory := (l2Step mem mu c0 n (k + 1)).memory }
      (l2Step mem mu c0 n (k + 1)).carry
      (UInt256.ofNat (ptrAt (pb + 32 * n - 32) i))
      (UInt256.ofNat (pa + 32 * n - 32)) (UInt256.ofNat (pb - 32))
      (isFour n) pdst ret rest) := by
  have hk : k + 1 < n := by omega
  have hp : 32 * (n - 2 - k) = 0 := by omega
  have hsize : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    decide
  have hpmj : ptrAt (32 * n - 64) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hptj : ptrAt (8192 + 32 * n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32 * (n - 2 - k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (8256 + 32 * (n - 2 - k)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  let st : State := { s with memory := (l2Step mem mu c0 n k).memory }
  let pm0 := UInt256.ofNat (ptrAt (32 * n - 64) k)
  let pt0 := UInt256.ofNat (ptrAt (8192 + 32 * n) k)
  have hM : UInt256.ofNat
      (MachineState.activeWordsAfter st.activeWords.toNat pm0.toNat 32) = st.activeWords := by
    simpa only [st, pm0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpmj] using hactM
  have hT : UInt256.ofNat
      (MachineState.activeWordsAfter st.activeWords.toNat pt0.toNat 32) = st.activeWords := by
    simpa only [st, pt0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hptj] using hactT
  have hload := CiosCachedL2.run_load st (UInt256.ofNat 5222) pm0 pt0
    (l2Step mem mu c0 n k).carry mu bi
    (UInt256.ofNat (ptrAt (pb + 32 * n - 32) i))
    (UInt256.ofNat (pa + 32 * n - 32)) (UInt256.ofNat (pb - 32))
    (isFour n) pdst ret rest hcap hM
  have hmac := CiosCachedMacCore.run_mac st
    (advancePC 3 (UInt256.ofNat 5222))
    (MachineState.readWord st.memory pm0.toNat) mu
    (l2Step mem mu c0 n k).carry pm0 pt0
    ([bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
      UInt256.ofNat (pa + 32 * n - 32), UInt256.ofNat (pb - 32),
      isFour n, negative32, allOnes, pdst, ret] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have hprefix := runInstructions_append_some _ _ _ _ _ hload hmac
  let sum := macSum (MachineState.readWord st.memory pm0.toNat) mu
    (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry
  let carry := macCarry (MachineState.readWord st.memory pm0.toNat) mu
    (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry
  let pbi := UInt256.ofNat (ptrAt (pb + 32 * n - 32) i)
  let paEnd := UInt256.ofNat (pa + 32 * n - 32)
  let pbEnd := UInt256.ofNat (pb - 32)
  let flag := isFour n
  have hprefix' :
      runInstructions prefixProgram
        (CiosCached.l2At 5222 s mem bi mu c0 pa pb n i k pdst ret rest) =
      some (framed st (UInt256.ofNat 5252)
        ([sum, pm0, pt0, carry, mu, bi, pbi, paEnd, pbEnd, flag,
          negative32, allOnes, pdst, ret] ++ rest)) := by
    simpa only [prefixProgram, CiosCached.l2At, CiosCachedL2.state, framed, st,
      sum, carry, pbi, paEnd, pbEnd, flag, advancePC,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod] using hprefix
  have htail := CiosCachedFixedL2Last.after_discard_eq st 5252 sum pm0 pt0 carry mu bi pbi
    paEnd pbEnd flag negative32 allOnes pdst ret rest (by omega)
  have htail' :
      runInstructions
          (CiosCachedFixedL2Last.fixedTail ++ CiosCachedFixedL2Last.discardPointers)
        (framed st (UInt256.ofNat 5252)
          ([sum, pm0, pt0, carry, mu, bi, pbi, paEnd, pbEnd, flag,
            negative32, allOnes, pdst, ret] ++ rest)) =
      runInstructions
          (CiosCachedFixedL2Last.oldTail ++ CiosCachedFixedL2Last.discardPointers)
        (framed st (UInt256.ofNat 5252)
          ([sum, pm0, pt0, carry, mu, bi, pbi, paEnd, pbEnd, flag,
            negative32, allOnes, pdst, ret] ++ rest)) := by
    simpa only [runProgram_eq, CiosCachedFixedL2Last.input, framed] using htail
  have hreplace :
      runInstructions
          (CiosCached.l2LastProgram ++ CiosCachedTailDefs.cleanupProgram)
          (CiosCached.l2At 5222 s mem bi mu c0 pa pb n i k pdst ret rest) =
        runInstructions
          (CiosCached.l2Program 0 ++ CiosCachedTailDefs.cleanupProgram)
          (CiosCached.l2At 5222 s mem bi mu c0 pa pb n i k pdst ret rest) := by
    rw [l2LastProgram_eq, l2Program0_eq, cleanupProgram_eq]
    rw [← List.append_assoc prefixProgram CiosCachedFixedL2Last.fixedTail,
      ← List.append_assoc prefixProgram CiosCachedFixedL2Last.oldTail]
    rw [runInstructions_append prefixProgram, runInstructions_append prefixProgram,
      hprefix']
    rw [← List.append_assoc CiosCachedFixedL2Last.fixedTail
        CiosCachedFixedL2Last.discardPointers,
      ← List.append_assoc CiosCachedFixedL2Last.oldTail
        CiosCachedFixedL2Last.discardPointers]
    rw [runInstructions_append
          (CiosCachedFixedL2Last.fixedTail ++ CiosCachedFixedL2Last.discardPointers),
      runInstructions_append
          (CiosCachedFixedL2Last.oldTail ++ CiosCachedFixedL2Last.discardPointers),
      htail']
  have hold := CiosCachedL2.run_step s (UInt256.ofNat 5222) mem bi mu c0 n k
    pbi paEnd pbEnd flag pdst ret rest hcap hact hn32 hk
  have hcleanup := CiosCachedTailStore.run_cleanup
    { s with memory := (l2Step mem mu c0 n (k + 1)).memory }
    (UInt256.ofNat (ptrAt (32 * n - 64) (k + 1)))
    (UInt256.ofNat (ptrAt (8192 + 32 * n) (k + 1)))
    (l2Step mem mu c0 n (k + 1)).carry mu bi pbi paEnd pbEnd flag pdst ret rest hcap
  have holdCleanup := runInstructions_append_some _ _ _ _ _ hold hcleanup
  rw [hreplace]
  simpa only [hp, CiosCachedL2.program_matches, CiosCachedL2.state,
    CiosCached.l2At, CiosCached.tailState, CiosCachedTailDefs.input,
    CiosCachedTailDefs.cleaned, CiosCachedTailDefs.baseStack, framed,
    Challenge.EvmProof.Word.ofNat_add_mod, pbi, paEnd, pbEnd, flag,
    List.cons_append, List.nil_append] using holdCleanup

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFixedL2LastRun

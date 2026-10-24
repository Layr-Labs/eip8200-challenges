import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Trace
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheLastTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore CiosCachedLast
theorem run_entry (w : Fin 33)
    (template : State) (pc x carry mu bi pbi paEnd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hpush : w.val = 0 → x = UInt256.ofNat 0)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat x.toNat 32) = template.activeWords) :
    runInstructions (CiosCachedLast.entryProgram w x)
      (framed template pc
        ([carry, mu, bi, pbi, paEnd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat (w.val + 8))
      ([UInt256.mulMod mu (MachineState.readWord template.memory x.toNat) maxWord, carry,
        mu * MachineState.readWord template.memory x.toNat, bi,
        pbi, paEnd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  by_cases hw : w.val = 0
  · have hx := hpush hw
    subst x
    have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
    change UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat 0 32) = template.activeWords at hactive
    simp [runInstructions, CiosCachedLast.entryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hw, hc11, hc12, hc13, hc14, hc15, State.activeWordsAfterUInt256, hzero, hactive, hN,
      succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
      List.exchange]
  · simp [runInstructions, CiosCachedLast.entryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hw, hc11, hc12, hc13, hc14, hc15, State.activeWordsAfterUInt256, hactive, hN,
      succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc,
      List.exchange]
    exact congrArg (fun n : Nat => pc + UInt256.ofNat n) (by omega)

/-- The frame after the last copy: `mu` is gone. -/
def lastState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [(l2Step mem mu c0 n k).carry, bi, pbi, paEnd, pbEnd, flag,
      tn, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }

/-- The last second-loop copy (cf. `TnCacheL2Trace.run_step`). -/
theorem run_stepLast (w : Fin 33) (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x tl ts : UInt256)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 2112 + 32 * (n - 2 - k))
    (hts : ts.toNat = 2112 + 32 * (n - 1 - k))
    (pbi paEnd pbEnd flag tn destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 88 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hk : k+1 < n)
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    runInstructions (l2LastProgram w x tl ts)
      (TnCacheL2Trace.state template pc mem bi mu c0 n k pbi paEnd pbEnd flag tn destination returnPC rest) =
    some (lastState template (pc + UInt256.ofNat (w.val + 33)) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag tn destination returnPC rest) := by
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat x.toNat 32) =
      st.activeWords := by simpa only [st, hx] using hactM
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by simpa only [st, htl] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat ts.toNat 32) =
      st.activeWords := by simpa only [st, hts] using hactW
  have hl := run_entry w st pc x (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag tn destination returnPC rest hrest hpush hM
  have hf := run_rest st (pc + UInt256.ofNat (w.val + 8))
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry tl ts
    ([bi, pbi, paEnd, pbEnd, flag, tn, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat (w.val + 8)) + UInt256.ofNat 25 =
      pc + UInt256.ofNat (w.val + 33) := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [l2LastProgram, TnCacheL2Trace.loadProgram, CiosCachedL2.loadProgram,
    st, TnCacheL2Trace.state, lastState, framed, l2Step, hx, htl, hts, hpc,
    List.cons_append, List.nil_append] using hall


#print axioms run_stepLast
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheLastTrace

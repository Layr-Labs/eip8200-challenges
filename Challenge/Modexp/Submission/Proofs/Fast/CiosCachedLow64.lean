import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLow64
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore
open CiosCachedL2

def cachedLoadProgram : List Instr :=
  [.op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨9, by decide⟩)]

theorem run_cached_load
    (template : State) (pc value carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hcache : rest[2]? = some value) :
    runInstructions cachedLoadProgram
      (framed template pc
        ([carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 2)
      ([maxWord, value, carry, mu, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [cachedLoadProgram, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hcache, hc11, hc12, hN, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

def cachedProgram (tl ts : UInt256) : List Instr :=
  (cachedLoadProgram ++ L2.productProgram) ++ L2.finishProgram tl ts

theorem run_cached_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x tl ts : UInt256)
    (hx : x.toNat = 32 * (n - 2 - k)) (hselect : x.toNat = 64) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n)
    (hcache : rest[2]? = some (MachineState.readWord mem 64)) :
    runInstructions (cachedProgram tl ts)
      (state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 34) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by simpa only [st, htl] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat ts.toNat 32) =
      st.activeWords := by simpa only [st, hts] using hactW
  have hpres : MachineState.readWord st.memory 64 = MachineState.readWord mem 64 :=
    readWord_l2Step mem mu c0 n 64 k hn (Or.inl (by decide))
  have hcacheStep : rest[2]? = some (MachineState.readWord st.memory x.toNat) := by
    simpa only [hselect, hpres] using hcache
  have hl := run_cached_load st pc (MachineState.readWord st.memory x.toNat)
    (l2Step mem mu c0 n k).carry mu bi pbi paEnd pbEnd flag destination returnPC rest hrest hcacheStep
  have hp := L2.run_product st (pc + UInt256.ofNat 2)
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 18 (pc + UInt256.ofNat 2))
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry tl ts
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 18 (pc + UInt256.ofNat 2) + UInt256.ofNat 14 =
      pc + UInt256.ofNat 34 := by
    simp [advancePC, succ_eq_add, word_add_assoc,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [cachedProgram, st, state, framed, l2Step, hx, htl, hts, hpc,
    List.cons_append, List.nil_append] using hall


#print axioms run_cached_load
#print axioms run_cached_step
end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLow64

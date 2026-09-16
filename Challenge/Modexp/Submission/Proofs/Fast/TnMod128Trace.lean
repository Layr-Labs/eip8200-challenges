import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Trace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

/-! A fourth cached modulus word, held in the former L2-target slot. The
instruction theorem is conditional on an explicit memory/cache invariant. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.TnMod128Trace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def loadProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨9, by decide⟩)]

theorem run_load (s : State)
    (pc carry mu bi pbi hd pb ent tn m128 inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions loadProgram
      (framed s pc ([carry,mu,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest)) =
    some (framed s (pc + UInt256.ofNat 2)
      ([maxWord,m128,carry,mu,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest)) := by
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  simp [loadProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, h11, h12, allOnes_value, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

def program : List Instr := loadProgram ++ macFusedProgram 2240 2272

/-- The third reduction cell of an eight-limb row, with arbitrary carry and
operands. The cached modulus word is preserved and no longer loaded from memory. -/
theorem run_step (s : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi hd pb ent tn m128 inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcache : m128 = MachineState.readWord mem 128) :
    runInstructions program
      (TnCacheL2Trace.state s pc mem bi mu c0 8 2 pbi hd pb ent tn m128 inv rest) =
    some (TnCacheL2Trace.state s (pc + UInt256.ofNat 33) mem bi mu c0 8 3
      pbi hd pb ent tn m128 inv rest) := by
  let st : State := {s with memory := (l2Step mem mu c0 8 2).memory}
  have hm : m128 = MachineState.readWord st.memory 128 := by
    rw [show MachineState.readWord st.memory 128 = MachineState.readWord mem 128 from
      readWord_l2Step mem mu c0 8 128 2 (by decide) (Or.inl (by decide))]
    exact hcache
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2240 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2240 32 (by decide) (by decide) hact
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2272 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2272 32 (by decide) (by decide) hact
  have h0 := run_load st pc (l2Step mem mu c0 8 2).carry mu bi pbi hd pb ent tn m128 inv rest hcap
  have h1 := CiosCachedFused.run_fused st (pc + UInt256.ofNat 2)
    m128 mu (l2Step mem mu c0 8 2).carry 2240 2272
    ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 2) + UInt256.ofNat 31 = pc + UInt256.ofNat 33 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have htl : (2240 : UInt256).toNat = 2240 := by decide
  have hts : (2272 : UInt256).toNat = 2272 := by decide
  simpa only [program, st, TnCacheL2Trace.state, framed, l2Step, hpc,
    hm, htl, hts, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    List.cons_append, List.nil_append] using h01

/-- The cached T-base distinguishes four and eight limbs without using the
register that has been repurposed for the modulus limb. -/
theorem width_tag (n : Nat) (hn : n = 4 ∨ n = 8) :
    UInt256.eq (UInt256.ofNat 2208) (UInt256.ofNat (2080+32*n)) =
      isFour n := by
  rcases hn with rfl | rfl <;> decide

theorem rebuild_entry (n : Nat) (hn : n = 4 ∨ n = 8) (base : UInt256) :
    UInt256.ofNat 14 * UInt256.land (UInt256.ofNat 128) (UInt256.ofNat (2080+32*n)) + base =
      UInt256.ofNat 1792 * isFour n + base := by
  rcases hn with rfl | rfl <;> rfl

#print axioms run_step
#print axioms width_tag
#print axioms rebuild_entry
end Challenge.Modexp.Submission.Proofs.Fast.TnMod128Trace

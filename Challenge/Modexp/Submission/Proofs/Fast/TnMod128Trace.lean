import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Trace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! A fourth cached modulus word, held in the former L2-target slot. The
instruction theorem is conditional on an explicit memory/cache invariant. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.TnMod128Trace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

def loadProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨9, by decide⟩)]

def fusedHead : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .MUL,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD]

def program : List Instr := fusedHead ++ CiosCached.macFusedPostProgramW3 2240 2272

private theorem add_comm_word (a b : UInt256) : a + b = b + a := by
  change UInt256.mk (a.val + b.val) = UInt256.mk (b.val + a.val)
  congr 1
  ac_rfl

private theorem run_fusedHead_state (s : State)
    (pc carry mu bi pbi hd pb ent tn m128 inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions fusedHead
      (framed s pc ([carry,mu,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest)) =
    some (framed s (pc + UInt256.ofNat 7)
      ([UInt256.mulMod mu m128 maxWord, m128 * mu, carry, mu, bi, pbi, hd, pb, ent, tn, allOnes, m128, inv] ++ rest)) := by
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  simp [fusedHead, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, List.exchange, Nat.add_assoc,
    h11, h12, h13, h14, h15, allOnes_value, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

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
  have h0 := run_fusedHead_state st pc (l2Step mem mu c0 8 2).carry mu bi pbi hd pb ent tn m128 inv rest hcap
  have h1 := CiosCachedFused.run_postW3 st (pc + UInt256.ofNat 7)
    (UInt256.mulMod mu m128 maxWord) (m128 * mu) (l2Step mem mu c0 8 2).carry mu 2240 2272
    ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hc : partialCarry m128 mu (l2Step mem mu c0 8 2).carry +
      UInt256.lt ((m128 * mu + (l2Step mem mu c0 8 2).carry) + MachineState.readWord st.memory (2240 : UInt256).toNat)
        (m128 * mu + (l2Step mem mu c0 8 2).carry) =
      macCarry m128 mu (MachineState.readWord st.memory (2240 : UInt256).toNat) (l2Step mem mu c0 8 2).carry := by
    rw [add_comm_word (partialCarry m128 mu (l2Step mem mu c0 8 2).carry)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm_word (m128 * mu + (l2Step mem mu c0 8 2).carry) (MachineState.readWord st.memory (2240 : UInt256).toNat)] using
      carry_eq m128 mu (MachineState.readWord st.memory (2240 : UInt256).toNat) (l2Step mem mu c0 8 2).carry
  have hs : (m128 * mu + (l2Step mem mu c0 8 2).carry) + MachineState.readWord st.memory (2240 : UInt256).toNat =
      macSum m128 mu (MachineState.readWord st.memory (2240 : UInt256).toNat) (l2Step mem mu c0 8 2).carry := by
    rw [add_comm_word]
    exact sum_eq m128 mu (MachineState.readWord st.memory (2240 : UInt256).toNat) (l2Step mem mu c0 8 2).carry
  change runInstructions (CiosCached.macFusedPostProgramW3 2240 2272) _ =
    some (framed _ _ ([partialCarry m128 mu (l2Step mem mu c0 8 2).carry + _, mu] ++ ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest))) at h1
  rw [hc, hs] at h1
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 26 = pc + UInt256.ofNat 33 := by
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

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

def program : List Instr := fusedHead ++ CiosCached.macFusedPostProgram 2240 2272

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

theorem run_step (s : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi hd pb ent tn m128 inv : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcache : m128 = MachineState.readWord mem 128) :
    runInstructions program
      (TnCacheL2Trace.state s pc mem bi mu c0 8 2 pbi hd pb ent tn m128 inv rest) =
    some (TnCacheL2Trace.state s (pc + UInt256.ofNat 32) mem bi mu c0 8 3
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
  have h1 := CiosCachedFused.run_post st (pc + UInt256.ofNat 7)
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
  change runInstructions (CiosCached.macFusedPostProgram 2240 2272) _ =
    some (framed _ _ ([partialCarry m128 mu (l2Step mem mu c0 8 2).carry + _, mu] ++ ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv] ++ rest))) at h1
  rw [hc, hs] at h1
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 25 = pc + UInt256.ofNat 32 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have htl : (2240 : UInt256).toNat = 2240 := by decide
  have hts : (2272 : UInt256).toNat = 2272 := by decide
  simpa only [program, st, TnCacheL2Trace.state, framed, l2Step, hpc,
    hm, htl, hts, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    List.cons_append, List.nil_append] using h01

/-! Layout V1: for eight limbs the `m0` frame slot (twelfth word) caches modulus[160],
so the second reduction cell multiplies from the stack instead of loading memory. -/
def fusedHead160 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .MUL,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD]

def program160 : List Instr := fusedHead160 ++ CiosCached.macFusedPostProgram 2272 2304

private theorem run_fusedHead160_state (s : State)
    (pc carry mu bi pbi hd pb ent tn m128 inv m160 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005) :
    runInstructions fusedHead160
      (framed s pc ([carry,mu,bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m160] ++ rest)) =
    some (framed s (pc + UInt256.ofNat 7)
      ([UInt256.mulMod mu m160 maxWord, m160 * mu, carry, mu, bi, pbi, hd, pb, ent, tn, allOnes, m128, inv, m160] ++ rest)) := by
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  have h16 : rest.length+16 < 1024 := by omega
  simp [fusedHead160, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, List.exchange, Nat.add_assoc,
    h12, h13, h14, h15, h16, allOnes_value, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_step160 (s : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi hd pb ent tn m128 inv m160 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcache : m160 = MachineState.readWord mem 160) :
    runInstructions program160
      (TnCacheL2Trace.state s pc mem bi mu c0 8 1 pbi hd pb ent tn m128 inv (m160 :: rest)) =
    some (TnCacheL2Trace.state s (pc + UInt256.ofNat 32) mem bi mu c0 8 2
      pbi hd pb ent tn m128 inv (m160 :: rest)) := by
  let st : State := {s with memory := (l2Step mem mu c0 8 1).memory}
  have hm : m160 = MachineState.readWord st.memory 160 := by
    rw [show MachineState.readWord st.memory 160 = MachineState.readWord mem 160 from
      readWord_l2Step mem mu c0 8 160 1 (by decide) (Or.inl (by decide))]
    exact hcache
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2272 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2272 32 (by decide) (by decide) hact
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2304 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2304 32 (by decide) (by decide) hact
  have h0 := run_fusedHead160_state st pc (l2Step mem mu c0 8 1).carry mu bi pbi hd pb ent tn m128 inv m160 rest hcap
  have h1 := CiosCachedFused.run_post st (pc + UInt256.ofNat 7)
    (UInt256.mulMod mu m160 maxWord) (m160 * mu) (l2Step mem mu c0 8 1).carry mu 2272 2304
    ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m160] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hc : partialCarry m160 mu (l2Step mem mu c0 8 1).carry +
      UInt256.lt ((m160 * mu + (l2Step mem mu c0 8 1).carry) + MachineState.readWord st.memory (2272 : UInt256).toNat)
        (m160 * mu + (l2Step mem mu c0 8 1).carry) =
      macCarry m160 mu (MachineState.readWord st.memory (2272 : UInt256).toNat) (l2Step mem mu c0 8 1).carry := by
    rw [add_comm_word (partialCarry m160 mu (l2Step mem mu c0 8 1).carry)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm_word (m160 * mu + (l2Step mem mu c0 8 1).carry) (MachineState.readWord st.memory (2272 : UInt256).toNat)] using
      carry_eq m160 mu (MachineState.readWord st.memory (2272 : UInt256).toNat) (l2Step mem mu c0 8 1).carry
  have hs : (m160 * mu + (l2Step mem mu c0 8 1).carry) + MachineState.readWord st.memory (2272 : UInt256).toNat =
      macSum m160 mu (MachineState.readWord st.memory (2272 : UInt256).toNat) (l2Step mem mu c0 8 1).carry := by
    rw [add_comm_word]
    exact sum_eq m160 mu (MachineState.readWord st.memory (2272 : UInt256).toNat) (l2Step mem mu c0 8 1).carry
  change runInstructions (CiosCached.macFusedPostProgram 2272 2304) _ =
    some (framed _ _ ([partialCarry m160 mu (l2Step mem mu c0 8 1).carry + _, mu] ++ ([bi,pbi,hd,pb,ent,tn,allOnes,m128,inv,m160] ++ rest))) at h1
  rw [hc, hs] at h1
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 25 = pc + UInt256.ofNat 32 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have htl : (2272 : UInt256).toNat = 2272 := by decide
  have hts : (2304 : UInt256).toNat = 2304 := by decide
  simpa only [program160, st, TnCacheL2Trace.state, framed, l2Step, hpc,
    hm, htl, hts, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    List.cons_append, List.nil_append] using h01

/-! P1a: the setup puts modulus[64] in the eleventh frame word (the Montgomery inverse rides in
the fifteenth), so the fifth reduction cell multiplies from the stack like the third. -/
def fusedHead64 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .MUL,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD]

def program64 : List Instr := fusedHead64 ++ CiosCached.macFusedPostProgram 2176 2208

private theorem run_fusedHead64_state (s : State)
    (pc carry mu bi pbi hd pb ent tn m128 m64 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions fusedHead64
      (framed s pc ([carry,mu,bi,pbi,hd,pb,ent,tn,allOnes,m128,m64] ++ rest)) =
    some (framed s (pc + UInt256.ofNat 7)
      ([UInt256.mulMod mu m64 maxWord, m64 * mu, carry, mu, bi, pbi, hd, pb, ent, tn, allOnes, m128, m64] ++ rest)) := by
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  simp [fusedHead64, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, List.exchange, Nat.add_assoc,
    h11, h12, h13, h14, h15, allOnes_value, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_step64 (s : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat)
    (pbi hd pb ent tn m128 m64 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : k + 4 = n)
    (hcache : m64 = MachineState.readWord mem 64) :
    runInstructions program64
      (TnCacheL2Trace.state s pc mem bi mu c0 n k pbi hd pb ent tn m128 m64 rest) =
    some (TnCacheL2Trace.state s (pc + UInt256.ofNat 32) mem bi mu c0 n (k+1)
      pbi hd pb ent tn m128 m64 rest) := by
  let st : State := {s with memory := (l2Step mem mu c0 n k).memory}
  have hm : m64 = MachineState.readWord st.memory 64 := by
    rw [show MachineState.readWord st.memory 64 = MachineState.readWord mem 64 from
      readWord_l2Step mem mu c0 n 64 k hn (Or.inl (by decide))]
    exact hcache
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2176 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2176 32 (by decide) (by decide) hact
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2208 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2208 32 (by decide) (by decide) hact
  have h0 := run_fusedHead64_state st pc (l2Step mem mu c0 n k).carry mu bi pbi hd pb ent tn m128 m64 rest hcap
  have h1 := CiosCachedFused.run_post st (pc + UInt256.ofNat 7)
    (UInt256.mulMod mu m64 maxWord) (m64 * mu) (l2Step mem mu c0 n k).carry mu 2176 2208
    ([bi,pbi,hd,pb,ent,tn,allOnes,m128,m64] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hc : partialCarry m64 mu (l2Step mem mu c0 n k).carry +
      UInt256.lt ((m64 * mu + (l2Step mem mu c0 n k).carry) + MachineState.readWord st.memory (2176 : UInt256).toNat)
        (m64 * mu + (l2Step mem mu c0 n k).carry) =
      macCarry m64 mu (MachineState.readWord st.memory (2176 : UInt256).toNat) (l2Step mem mu c0 n k).carry := by
    rw [add_comm_word (partialCarry m64 mu (l2Step mem mu c0 n k).carry)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm_word (m64 * mu + (l2Step mem mu c0 n k).carry) (MachineState.readWord st.memory (2176 : UInt256).toNat)] using
      carry_eq m64 mu (MachineState.readWord st.memory (2176 : UInt256).toNat) (l2Step mem mu c0 n k).carry
  have hs : (m64 * mu + (l2Step mem mu c0 n k).carry) + MachineState.readWord st.memory (2176 : UInt256).toNat =
      macSum m64 mu (MachineState.readWord st.memory (2176 : UInt256).toNat) (l2Step mem mu c0 n k).carry := by
    rw [add_comm_word]
    exact sum_eq m64 mu (MachineState.readWord st.memory (2176 : UInt256).toNat) (l2Step mem mu c0 n k).carry
  change runInstructions (CiosCached.macFusedPostProgram 2176 2208) _ =
    some (framed _ _ ([partialCarry m64 mu (l2Step mem mu c0 n k).carry + _, mu] ++ ([bi,pbi,hd,pb,ent,tn,allOnes,m128,m64] ++ rest))) at h1
  rw [hc, hs] at h1
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 25 = pc + UInt256.ofNat 32 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have htl : (2176 : UInt256).toNat = 2176 := by decide
  have hts : (2208 : UInt256).toNat = 2208 := by decide
  have hk2 : n - 2 - k = 2 := by omega
  have hk1 : n - 1 - k = 3 := by omega
  simpa only [program64, st, TnCacheL2Trace.state, framed, l2Step, hpc,
    hm, htl, hts, hk2, hk1, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    List.cons_append, List.nil_append] using h01

/-! P1b: the setup puts modulus[32] in the eighth cell-frame word (the carry cache rides in the
sixteenth), so the sixth reduction cell also multiplies from the stack. -/
def fusedHead32 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op .MUL,
   .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨9, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD]

def program32 : List Instr := fusedHead32 ++ CiosCached.macFusedPostProgram 2144 2176

private theorem run_fusedHead32_state (s : State)
    (pc carry mu bi pbi hd pb ent m32 m128 m64 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions fusedHead32
      (framed s pc ([carry,mu,bi,pbi,hd,pb,ent,m32,allOnes,m128,m64] ++ rest)) =
    some (framed s (pc + UInt256.ofNat 7)
      ([UInt256.mulMod mu m32 maxWord, m32 * mu, carry, mu, bi, pbi, hd, pb, ent, m32, allOnes, m128, m64] ++ rest)) := by
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  simp [fusedHead32, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, List.exchange, Nat.add_assoc,
    h11, h12, h13, h14, h15, allOnes_value, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_step32 (s : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat)
    (pbi hd pb ent m32 m128 m64 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : k + 3 = n)
    (hcache : m32 = MachineState.readWord mem 32) :
    runInstructions program32
      (TnCacheL2Trace.state s pc mem bi mu c0 n k pbi hd pb ent m32 m128 m64 rest) =
    some (TnCacheL2Trace.state s (pc + UInt256.ofNat 32) mem bi mu c0 n (k+1)
      pbi hd pb ent m32 m128 m64 rest) := by
  let st : State := {s with memory := (l2Step mem mu c0 n k).memory}
  have hm : m32 = MachineState.readWord st.memory 32 := by
    rw [show MachineState.readWord st.memory 32 = MachineState.readWord mem 32 from
      readWord_l2Step mem mu c0 n 32 k hn (Or.inl (by decide))]
    exact hcache
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2144 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2144 32 (by decide) (by decide) hact
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (2176 : UInt256).toNat 32) = st.activeWords :=
    activeWords_fix s 2176 32 (by decide) (by decide) hact
  have h0 := run_fusedHead32_state st pc (l2Step mem mu c0 n k).carry mu bi pbi hd pb ent m32 m128 m64 rest hcap
  have h1 := CiosCachedFused.run_post st (pc + UInt256.ofNat 7)
    (UInt256.mulMod mu m32 maxWord) (m32 * mu) (l2Step mem mu c0 n k).carry mu 2144 2176
    ([bi,pbi,hd,pb,ent,m32,allOnes,m128,m64] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hc : partialCarry m32 mu (l2Step mem mu c0 n k).carry +
      UInt256.lt ((m32 * mu + (l2Step mem mu c0 n k).carry) + MachineState.readWord st.memory (2144 : UInt256).toNat)
        (m32 * mu + (l2Step mem mu c0 n k).carry) =
      macCarry m32 mu (MachineState.readWord st.memory (2144 : UInt256).toNat) (l2Step mem mu c0 n k).carry := by
    rw [add_comm_word (partialCarry m32 mu (l2Step mem mu c0 n k).carry)]
    simpa only [UInt256.gt, UInt256.lt,
      add_comm_word (m32 * mu + (l2Step mem mu c0 n k).carry) (MachineState.readWord st.memory (2144 : UInt256).toNat)] using
      carry_eq m32 mu (MachineState.readWord st.memory (2144 : UInt256).toNat) (l2Step mem mu c0 n k).carry
  have hs : (m32 * mu + (l2Step mem mu c0 n k).carry) + MachineState.readWord st.memory (2144 : UInt256).toNat =
      macSum m32 mu (MachineState.readWord st.memory (2144 : UInt256).toNat) (l2Step mem mu c0 n k).carry := by
    rw [add_comm_word]
    exact sum_eq m32 mu (MachineState.readWord st.memory (2144 : UInt256).toNat) (l2Step mem mu c0 n k).carry
  change runInstructions (CiosCached.macFusedPostProgram 2144 2176) _ =
    some (framed _ _ ([partialCarry m32 mu (l2Step mem mu c0 n k).carry + _, mu] ++ ([bi,pbi,hd,pb,ent,m32,allOnes,m128,m64] ++ rest))) at h1
  rw [hc, hs] at h1
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hpc : (pc + UInt256.ofNat 7) + UInt256.ofNat 25 = pc + UInt256.ofNat 32 := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have htl : (2144 : UInt256).toNat = 2144 := by decide
  have hts : (2176 : UInt256).toNat = 2176 := by decide
  have hk2 : n - 2 - k = 1 := by omega
  have hk1 : n - 1 - k = 2 := by omega
  simpa only [program32, st, TnCacheL2Trace.state, framed, l2Step, hpc,
    hm, htl, hts, hk2, hk1, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    List.cons_append, List.nil_append] using h01

theorem width_tag (n : Nat) (hn : n = 4 ∨ n = 8) :
    UInt256.eq (UInt256.ofNat 2208) (UInt256.ofNat (2080+32*n)) =
      isFour n := by
  rcases hn with rfl | rfl <;> decide

theorem rebuild_entry (n : Nat) (hn : n = 4 ∨ n = 8) (base : UInt256) :
    UInt256.ofNat 14 * UInt256.land (UInt256.ofNat 128) (UInt256.ofNat (2080+32*n)) + base =
      UInt256.ofNat 1792 * isFour n + base := by
  rcases hn with rfl | rfl <;> rfl

end Challenge.Modexp.Submission.Proofs.Fast.TnMod128Trace

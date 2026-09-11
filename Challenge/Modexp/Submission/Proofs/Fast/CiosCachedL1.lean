import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
Generic first-loop MAC execution against the unchanged MONPRO memory
recursion.  The accumulator limb address is an immediate; no Artifact,
concrete program counter, gas schedule or whole-candidate claim.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

/-- The cached word is the actual operand base; there is no physical cursor. -/
def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [(l1Step mem bi pa n j).carry, bi, pbi, UInt256.ofNat pa,
      pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest
    memory := (l1Step mem bi pa n j).memory }

def doneState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n : Nat) (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  state template pc mem bi pa n n pbi pbEnd flag destination returnPC rest

def loadProgram (off : UInt256) : List Instr := l1LoadProgram off

def lastLoadProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op .MLOAD, .op (.Dup ⟨8, by decide⟩)]

theorem program_eq (off t : UInt256) :
    l1Program off t = (loadProgram off ++ L2.productProgram) ++ L2.finishProgram t t := rfl

theorem first_eq (off t : UInt256) :
    l1FirstProgram off t =
      (loadProgram off ++ L2.zeroProductProgram) ++ L2.finishProgram t t := rfl

theorem last_eq (t : UInt256) :
    l1LastProgram t = (lastLoadProgram ++ L2.productProgram) ++ L2.finishProgram t t := rfl

/-- Keep symbolic word conversion outside the large execution proof. -/
theorem base_offset_toNat (pa : Nat) (off : UInt256) (hfit : pa + off.toNat ≤ 9472) :
    (UInt256.ofNat pa + off).toNat = pa + off.toNat := by
  have hpa : pa < 2 ^ 256 := by omega
  have hsum : pa + off.toNat < 2 ^ 256 := by omega
  rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hpa, Nat.mod_eq_of_lt hsum]

theorem run_load (template : State)
    (pc off carry bi pbi paBase pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (paBase + off).toNat 32) = template.activeWords) :
    runInstructions (loadProgram off)
      (framed template pc
        ([carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 6)
      ([maxWord, MachineState.readWord template.memory (paBase + off).toNat,
        carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    show (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      from by decide] at hactive
  simp [runInstructions, loadProgram, l1LoadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, State.activeWordsAfterUInt256, hactive, hN, succ_eq_add,
    word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_last_load (template : State)
    (pc carry bi pbi paBase pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat paBase.toNat 32) = template.activeWords) :
    runInstructions lastLoadProgram
      (framed template pc
        ([carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 3 pc)
      ([maxWord, MachineState.readWord template.memory paBase.toNat,
        carry, bi, pbi, paBase, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, lastLoadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc10, hc11, State.activeWordsAfterUInt256, hactive, hN]

/-- Ordinary first-loop cell at the cached base plus its immediate offset. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (_hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1Program off t)
      (state template pc mem bi pa n j pbi pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 38) mem bi pa n (j+1)
      pbi pbEnd flag destination returnPC rest) := by
  have haddr : (UInt256.ofNat pa + off).toNat = pa + 32*(n-1-j) := by
    rw [base_offset_toNat pa off (by omega), hoff]
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (pa + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l1Step mem bi pa n j).memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat pa + off).toNat 32) = st.activeWords := by
    simpa only [st, haddr] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_load st pc off (l1Step mem bi pa n j).carry bi pbi (UInt256.ofNat pa)
    pbEnd flag destination returnPC rest hrest hA
  have hp := L2.run_product st (pc + UInt256.ofNat 6)
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (l1Step mem bi pa n j).carry
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 18 (pc + UInt256.ofNat 6))
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (l1Step mem bi pa n j).carry t t
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 18 (pc + UInt256.ofNat 6) + UInt256.ofNat 14 =
      pc + UInt256.ofNat 38 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program_eq, st, state, framed, l1Step, haddr, ht, hpc,
    List.cons_append, List.nil_append] using hall

/-- The first cell of a row has zero carry by definition, not by a new caller assumption. -/
theorem run_first (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1)) (ht : t.toNat = 8256 + 32 * (n - 1))
    (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (_hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1FirstProgram off t)
      (state template pc mem bi pa n 0 pbi pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 35) mem bi pa n 1
      pbi pbEnd flag destination returnPC rest) := by
  have haddr : (UInt256.ofNat pa + off).toNat = pa + 32*(n-1) := by
    rw [base_offset_toNat pa off (by omega), hoff]
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (pa + 32*(n-1)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := mem }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat pa + off).toNat 32) = st.activeWords := by
    simpa only [st, haddr] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_load st pc off (UInt256.ofNat 0) bi pbi (UInt256.ofNat pa)
    pbEnd flag destination returnPC rest hrest hA
  have hp := L2.run_product_zero st (pc + UInt256.ofNat 6)
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 15 (pc + UInt256.ofNat 6))
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (UInt256.ofNat 0) t t
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 15 (pc + UInt256.ofNat 6) + UInt256.ofNat 14 =
      pc + UInt256.ofNat 35 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [first_eq, st, state, framed, l1Step, haddr, ht, hpc,
    Nat.sub_zero, List.cons_append, List.nil_append] using hall

/-- Terminal cell loads directly at the cached base. -/
theorem run_last (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n : Nat) (t : UInt256) (ht : t.toNat = 8256)
    (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (_hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1LastProgram t)
      (state template pc mem bi pa n (n-1) pbi pbEnd flag destination returnPC rest) =
    some (doneState template (pc + UInt256.ofNat 35) mem bi pa n
      pbi pbEnd flag destination returnPC rest) := by
  have hpaNat : (UInt256.ofNat pa).toNat = pa := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat pa 32) =
      template.activeWords := activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat 8256 32) =
      template.activeWords := activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l1Step mem bi pa n (n-1)).memory }
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat pa).toNat 32) = st.activeWords := by
    simpa only [st, hpaNat] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by simpa only [st, ht] using hactT
  have hl := run_last_load st pc (l1Step mem bi pa n (n-1)).carry bi pbi
    (UInt256.ofNat pa) pbEnd flag destination returnPC rest hrest hA
  have hp := L2.run_product st (advancePC 3 pc)
    (MachineState.readWord st.memory (UInt256.ofNat pa).toNat) bi
    (l1Step mem bi pa n (n-1)).carry
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 18 (advancePC 3 pc))
    (MachineState.readWord st.memory (UInt256.ofNat pa).toNat) bi
    (l1Step mem bi pa n (n-1)).carry t t
    ([pbi, UInt256.ofNat pa, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 18 (advancePC 3 pc) + UInt256.ofNat 14 = pc + UInt256.ofNat 35 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have hnn : n-1+1 = n := by omega
  have hfinal : runInstructions (l1LastProgram t)
      (state template pc mem bi pa n (n-1) pbi pbEnd flag destination returnPC rest) =
      some (state template (pc + UInt256.ofNat 35) mem bi pa n (n-1+1)
        pbi pbEnd flag destination returnPC rest) := by
    simpa only [last_eq, st, state, framed, l1Step, hpaNat, ht, hpc,
      Nat.sub_self, Nat.mul_zero, Nat.add_zero, List.cons_append, List.nil_append] using hall
  simpa only [hnn, doneState] using hfinal

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

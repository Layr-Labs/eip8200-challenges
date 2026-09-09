import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
Generic cached MAC execution against the unchanged MONPRO memory recursion.
No Artifact, concrete program counter, gas schedule or whole-candidate claim.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def program (c : Nat) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .push ⟨2, by decide⟩ (UInt256.ofNat c),
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
      UInt256.ofNat (ptrAt (8224 + 32 * n) j),
      (l1Step mem bi pa n j).carry, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l1Step mem bi pa n j).memory }


def loadProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

/-- `c` is the scratch pointer decremented by one limb.  The artifact pushes it
as a literal instead of recomputing `Dup;Dup;ADD` each iteration; `c` is a
parameter here because the eight unrolled copies carry eight different literals.
`PUSH2` is three bytes, exactly what the three folded opcodes were, so every
`advancePC` and every pc claim downstream is unchanged. -/
def tailProgram (c : Nat) : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat c),
   .op (.Swap ⟨2, by decide⟩), .op .MSTORE, .op (.Dup ⟨8, by decide⟩), .op .ADD]

theorem program_eq (c : Nat) :
    program c = (loadProgram ++ CiosCachedMacCore.program) ++ tailProgram c := rfl

theorem run_load (template : State) (pc pa pt carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pa.toNat 32) = template.activeWords) :
    runInstructions loadProgram
      (framed template pc
        ([pa, pt, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 3 pc)
      ([maxWord, MachineState.readWord template.memory pa.toNat, pa, pt, carry, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 12 < 1024 := by omega
  have hc12 : rest.length + 13 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc11, hc12, State.activeWordsAfterUInt256, hactive, hN]

theorem run_tail (template : State) (pc pa pt sum carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (c : Nat) (hc : UInt256.ofNat c = negative32 + pt)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pt.toNat 32) = template.activeWords) :
    runInstructions (tailProgram c)
      (framed template pc
        ([sum, pa, pt, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) pt.toNat }
      (advancePC 7 pc)
      ([negative32 + pa, negative32 + pt, carry, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 12 < 1024 := by omega
  have hc12 : rest.length + 13 < 1024 := by omega
  have hc13 : rest.length + 14 < 1024 := by omega
  simp [runInstructions, tailProgram, framed, Challenge.EvmProof.Stepper.runInstr, hc,
    advancePC, hc11, hc12, hc13, List.exchange,
    State.activeWordsAfterUInt256, hactive]
  simp [succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- One copy works also at j=n-1; its following loop test is separate. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (program (ptrAt (8224 + 32*n) j - 32))
      (state template pc mem bi pa n j pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 37) mem bi pa n (j+1)
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
  have hl := run_load st pc pa0 pt0 (l1Step mem bi pa n j).carry bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hA
  have hm := CiosCachedMacCore.run_mac st (advancePC 3 pc)
    (MachineState.readWord st.memory pa0.toNat) bi (l1Step mem bi pa n j).carry pa0 pt0
    ([pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have hcdef : UInt256.ofNat (ptrAt (8224 + 32*n) j - 32) = negative32 + pt0 := by
    have hb : 32 ≤ ptrAt (8224 + 32*n) j := by
      simp only [ptrAt]; omega
    simp only [pt0]
    rw [hK, Challenge.EvmProof.Word.ofNat_add_mod]
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_ofNat]
    have heq :
        115792089237316195423570985008687907853269984665640564039457584007913129639904 + ptrAt (8224 + 32*n) j =
        (ptrAt (8224 + 32*n) j - 32) + 2 ^ 256 := by omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
  have ht := run_tail st (advancePC 9 (advancePC 18 (advancePC 3 pc))) pa0 pt0
    (macSum (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory pt0.toNat) (l1Step mem bi pa n j).carry)
    (macCarry (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory pt0.toNat) (l1Step mem bi pa n j).carry)
    bi pbi paEnd pbEnd flag destination returnPC (ptrAt (8224 + 32*n) j - 32) hcdef
    rest hrest hT
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both ht
  have hpc : advancePC 7 (advancePC 9 (advancePC 18 (advancePC 3 pc))) =
      pc + UInt256.ofNat 37 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program_eq (ptrAt (8224 + 32*n) j - 32), st, pa0, pt0, state, framed, l1Step,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpaj, hptj, hpc, hK,
    Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ] using hall

theorem program_matches (c : Nat) : program c = CiosCached.l1Program c := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

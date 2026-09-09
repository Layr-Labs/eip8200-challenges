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

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
      (l1Step mem bi pa n j).carry, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l1Step mem bi pa n j).memory }

/-- After the final copy the exhausted cursor is gone. -/
def doneState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [(l1Step mem bi pa n n).carry, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l1Step mem bi pa n n).memory }

def loadProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def storeProgram (t : UInt256) : List Instr :=
  [.push 2 t, .op .MSTORE]

def advanceProgram : List Instr :=
  [.op (.Dup ⟨7, by decide⟩), .op .ADD]

def dropProgram : List Instr :=
  [.op .POP]

theorem body_eq (t : UInt256) :
    l1Body t = (loadProgram ++ L1.program t) ++ storeProgram t := rfl

theorem program_eq (t : UInt256) :
    l1Program t = l1Body t ++ advanceProgram := rfl

theorem last_eq (t : UInt256) :
    l1LastProgram t = l1Body t ++ dropProgram := rfl

theorem run_load (template : State) (pc pa carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pa.toNat 32) = template.activeWords) :
    runInstructions loadProgram
      (framed template pc
        ([pa, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 3 pc)
      ([maxWord, MachineState.readWord template.memory pa.toNat, pa, carry, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc11, hc12, State.activeWordsAfterUInt256, hactive, hN]

theorem run_store (template : State) (pc sum pa carry bi pbi paEnd pbEnd flag destination returnPC t : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (storeProgram t)
      (framed template pc
        ([sum, pa, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) t.toNat }
      (pc + UInt256.ofNat 4)
      ([pa, carry, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [runInstructions, storeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc12, hc13, State.activeWordsAfterUInt256, hactive, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_advance (template : State) (pc pa carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runInstructions advanceProgram
      (framed template pc
        ([pa, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 2 pc)
      ([negative32 + pa, carry, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [runInstructions, advanceProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc11, hc12]

theorem run_drop (template : State) (pc pa carry bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runInstructions dropProgram
      (framed template pc
        ([pa, carry, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 1 pc)
      ([carry, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [runInstructions, dropProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc11]

/-- The cursor-free body: memory and carry advance, the cursor is left on top. -/
theorem run_body (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (t : UInt256) (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1Body t) (state template pc mem bi pa n j pbi paEnd pbEnd flag destination returnPC rest) =
    some (framed { template with memory := (l1Step mem bi pa n (j+1)).memory }
      (pc + UInt256.ofNat 36)
      ([UInt256.ofNat (ptrAt (pa + 32 * n - 32) j), (l1Step mem bi pa n (j+1)).carry, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hsize : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  have hpaj : ptrAt (pa + 32*n - 32) j %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pa + 32*(n-1-j) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hactA : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (pa + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-j)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l1Step mem bi pa n j).memory }
  let pa0 := UInt256.ofNat (ptrAt (pa + 32*n - 32) j)
  have hA : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat pa0.toNat 32) =
      st.activeWords := by
    simpa only [st, pa0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpaj] using hactA
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by
    simpa only [st, ht] using hactT
  have hl := run_load st pc pa0 (l1Step mem bi pa n j).carry bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hA
  have hm := L1.run_mac st (advancePC 3 pc)
    (MachineState.readWord st.memory pa0.toNat) bi (l1Step mem bi pa n j).carry pa0 t
    ([pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have hs := run_store st (advancePC 6 (advancePC 18 (advancePC 3 pc) + UInt256.ofNat 5))
    (macSum (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory t.toNat) (l1Step mem bi pa n j).carry)
    pa0
    (macCarry (MachineState.readWord st.memory pa0.toNat) bi
      (MachineState.readWord st.memory t.toNat) (l1Step mem bi pa n j).carry)
    bi pbi paEnd pbEnd flag destination returnPC t rest hrest hT
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both hs
  have hpc : advancePC 6 (advancePC 18 (advancePC 3 pc) + UInt256.ofNat 5) + UInt256.ofNat 4 =
      pc + UInt256.ofNat 36 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [body_eq, st, pa0, state, framed, l1Step,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpaj, ht, hpc] using hall

/-- One copy of the cursor-advancing MAC. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (t : UInt256) (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1Program t) (state template pc mem bi pa n j pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 38) mem bi pa n (j+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    (by decide)
  have hb := run_body template pc mem bi pa n j t ht pbi paEnd pbEnd flag destination returnPC
    rest hrest hactive hn hj hpa hpaFit
  have ha := run_advance { template with memory := (l1Step mem bi pa n (j+1)).memory }
    (pc + UInt256.ofNat 36) (UInt256.ofNat (ptrAt (pa + 32 * n - 32) j))
    (l1Step mem bi pa n (j+1)).carry bi pbi paEnd pbEnd flag destination returnPC rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hb ha
  have hpc : advancePC 2 (pc + UInt256.ofNat 36) = pc + UInt256.ofNat 38 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program_eq, state, framed, hpc, hK,
    Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ] using hall

/-- The final copy of a row drops the cursor. -/
theorem run_last (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n : Nat) (t : UInt256) (ht : t.toNat = 8256)
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (l1LastProgram t) (state template pc mem bi pa n (n-1) pbi paEnd pbEnd flag destination returnPC rest) =
    some (doneState template (pc + UInt256.ofNat 37) mem bi pa n
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have ht' : t.toNat = 8256 + 32 * (n - 1 - (n - 1)) := by
    rw [ht]; simp
  have hb := run_body template pc mem bi pa n (n-1) t ht' pbi paEnd pbEnd flag destination returnPC
    rest hrest hactive hn (by omega) hpa hpaFit
  have hd := run_drop { template with memory := (l1Step mem bi pa n (n-1+1)).memory }
    (pc + UInt256.ofNat 36) (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (n-1)))
    (l1Step mem bi pa n (n-1+1)).carry bi pbi paEnd pbEnd flag destination returnPC rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hb hd
  have hpc : advancePC 1 (pc + UInt256.ofNat 36) = pc + UInt256.ofNat 37 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  have hnn : n - 1 + 1 = n := by omega
  simpa only [last_eq, doneState, framed, hpc, hnn] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2TailWords

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Const

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def loadProgram (p : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat p), .op .MLOAD, .op (.Dup ⟨11, by decide⟩)]

def readProgram (p : Nat) : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .push 2 (UInt256.ofNat (8256+p)), .op .MLOAD]

def storeProgram (p : Nat) : List Instr :=
  [.push 4 (UInt256.ofNat (8288+p)), .op .MSTORE]

def program (p : Nat) : List Instr :=
  (((loadProgram p ++ CiosCachedMacCore.productProgram) ++ readProgram p) ++
    CiosCachedMacCore.sumProgram) ++ storeProgram p

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (32*n-64), UInt256.ofNat (8192+32*n),
      (l2Step mem mu c0 n k).carry, mu, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }

theorem run_load (p : Nat) (template : State)
    (pc pm pt carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat p).toNat 32) = template.activeWords) :
    runInstructions (loadProgram p)
      (framed template pc
        ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([maxWord, MachineState.readWord template.memory (UInt256.ofNat p).toNat,
        pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by decide] at hactive
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc13, hc14, State.activeWordsAfterUInt256, hactive, hN,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_read (p : Nat) (template : State) (pc part pm pt sum y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat (8256+p)).toNat 32) = template.activeWords) :
    runInstructions (readProgram p)
      (framed template pc ([part, pm, pt, sum, y] ++ rest)) =
    some (framed template (advancePC 5 pc)
      ([MachineState.readWord template.memory (UInt256.ofNat (8256+p)).toNat,
        sum, part, pm, pt, sum, y] ++ rest)) := by
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by decide] at hactive
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, readProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc5, hc6, hc7, State.activeWordsAfterUInt256, hactive,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_store (p : Nat) (template : State) (pc sum : UInt256)
    (stack : List UInt256) (hrest : stack.length + 2 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat (8288+p)).toNat 32) = template.activeWords) :
    runInstructions (storeProgram p) (framed template pc (sum :: stack)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) (UInt256.ofNat (8288+p)).toNat }
      (pc + UInt256.ofNat 6) stack) := by
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat,
    show (2 : Nat)^256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 from by decide] at hactive
  have hc1 : stack.length + 1 < 1024 := by omega
  simp [runInstructions, storeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hrest, hc1, State.activeWordsAfterUInt256, hactive,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_words (p : Nat) (template : State)
    (pc pm pt carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hM : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat p).toNat 32) = template.activeWords)
    (hT : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat (8256+p)).toNat 32) = template.activeWords)
    (hW : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (UInt256.ofNat (8288+p)).toNat 32) = template.activeWords) :
    runInstructions (program p)
      (framed template pc
        ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord template.memory (UInt256.ofNat p).toNat) mu
              (MachineState.readWord template.memory (UInt256.ofNat (8256+p)).toNat) carry).toNat 32)
          (UInt256.ofNat (8288+p)).toNat }
      (pc + UInt256.ofNat 40)
      ([pm, pt,
        macCarry (MachineState.readWord template.memory (UInt256.ofNat p).toNat) mu
          (MachineState.readWord template.memory (UInt256.ofNat (8256+p)).toNat) carry,
        mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  let x := MachineState.readWord template.memory (UInt256.ofNat p).toNat
  let t := MachineState.readWord template.memory (UInt256.ofNat (8256+p)).toNat
  let more := [bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest
  have hc : more.length + 8 < 1024 := by
    simp only [more, List.length_append, List.length_cons, List.length_nil]
    omega
  have hl := run_load p template pc pm pt carry mu bi pbi paEnd pbEnd flag destination returnPC rest hrest hM
  have hm := CiosCachedMacCore.run_product template (pc + UInt256.ofNat 5)
    x mu carry pm pt more hc
  have hr := run_read p template (advancePC 18 (pc + UInt256.ofNat 5))
    (partialCarry x mu carry) pm pt (x*mu+carry) mu more hc hT
  have hs := CiosCachedMacCore.run_sum template
    (advancePC 5 (advancePC 18 (pc + UInt256.ofNat 5)))
    t (x*mu+carry) (partialCarry x mu carry) mu pm pt more hc
  rw [carry_eq, sum_eq] at hs
  have hw := run_store p template
    (advancePC 6 (advancePC 5 (advancePC 18 (pc + UInt256.ofNat 5))))
    (macSum x mu t carry) ([pm, pt, macCarry x mu t carry, mu] ++ more)
    (by simp only [more, List.length_append, List.length_cons, List.length_nil]; omega) hW
  have h1 := runInstructions_append_some _ _ _ _ _ hl hm
  have h2 := runInstructions_append_some _ _ _ _ _ h1 hr
  have h3 := runInstructions_append_some _ _ _ _ _ h2 hs
  have h4 := runInstructions_append_some _ _ _ _ _ h3 hw
  have hpc : advancePC 6 (advancePC 5 (advancePC 18 (pc + UInt256.ofNat 5))) + UInt256.ofNat 6 =
      pc + UInt256.ofNat 40 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program, more, List.cons_append, List.nil_append, x, t, hpc] using h4

theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n) :
    runInstructions (program (32*(n-2-k)))
      (state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 40) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  let p := 32*(n-2-k)
  have hp : p ≤ 960 := by dsimp [p]; omega
  have hsize : (2 : Nat)^256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  have hpM : (UInt256.ofNat p).toNat = p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by rw [hsize]; omega)]
  have hpT : (UInt256.ofNat (8256+p)).toNat = 8256+p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by rw [hsize]; omega)]
  have hpW : (UInt256.ofNat (8288+p)).toNat = 8288+p := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by rw [hsize]; omega)]
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat p).toNat 32) = st.activeWords := by
    rw [hpM]
    exact activeWords_fix st p 32 (by decide) (by omega) hactive
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat (8256+p)).toNat 32) = st.activeWords := by
    rw [hpT]
    exact activeWords_fix st (8256+p) 32 (by decide) (by omega) hactive
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (UInt256.ofNat (8288+p)).toNat 32) = st.activeWords := by
    rw [hpW]
    exact activeWords_fix st (8288+p) 32 (by decide) (by omega) hactive
  have haddr : 8288+p = 8256+32*(n-1-k) := by dsimp [p]; omega
  have hall := run_words p st pc (UInt256.ofNat (32*n-64)) (UInt256.ofNat (8192+32*n))
    (l2Step mem mu c0 n k).carry mu bi pbi paEnd pbEnd flag destination returnPC rest
    hrest hM hT hW
  simp only [hpM, hpT, hpW] at hall
  simpa only [haddr, p, state, st, framed, l2Step] using hall

theorem program_matches (p : Nat) : program p = CiosCached.l2ConstProgram p := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Const

import Challenge.Modexp.Submission.Proofs.Fast.CiosOperandCache
import Challenge.Modexp.Submission.Proofs.Fast.CiosCarryL1

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCarryOperand
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached CiosCachedMacCore CiosOperandCache
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
variable {carrySlot : UInt256}

def extendedStack (carry bi pbi pa pb flag target2 inv m0 tl a96 a64 a32 aLast dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [carry,bi,pbi,pa,pb,flag,carrySlot,allOnes,target2,inv,m0,tl,a96,a64,a32,aLast,dst,ret] ++ rest

def extraLoad (slot : Fin 3) : List Instr :=
  [.op (.Dup ⟨12+slot.val, by omega⟩), .op (.Dup ⟨8, by decide⟩)]

theorem run_extraLoad (slot : Fin 3) (s : State)
    (pc carry bi pbi pa pb flag target2 inv m0 tl a96 a64 a32 aLast dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions (extraLoad slot)
      (framed s pc (extendedStack (carrySlot := carrySlot) carry bi pbi pa pb flag target2 inv m0 tl a96 a64 a32 aLast dst ret rest)) =
    some (framed s (pc+UInt256.ofNat 2)
      ([maxWord,cacheWord slot a96 a64 a32] ++
        extendedStack (carrySlot := carrySlot) carry bi pbi pa pb flag target2 inv m0 tl a96 a64 a32 aLast dst ret rest)) := by
  have hc18 : rest.length+18 < 1024 := by omega
  have hc19 : rest.length+19 < 1024 := by omega
  fin_cases slot <;>
    simp [extraLoad, cacheWord, extendedStack, runInstructions, Challenge.EvmProof.Stepper.runInstr,
      framed, Nat.add_assoc, hc18, hc19, allOnes_value, succ_eq_add, word_add_assoc,
      Challenge.EvmProof.Word.ofNat_add_mod]

def extraProgram (slot : Fin 3) (t : UInt256) : List Instr :=
  (extraLoad slot ++ L2.productProgram) ++ L2.finishProgram t t

theorem run_step (slot : Fin 3) (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32*(n-1-j)) (hselect : off.toNat = cacheAddress slot)
    (ht : t.toNat = 8256+32*(n-1-j))
    (pbi pbEnd flag target2 inv m0 tl a96 a64 a32 aLast dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 998)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hfour : 4 ≤ n)
    (hj : j < n) (hpaFit : pa+32*n ≤ 8192)
    (hc : OperandCache mem pa n a96 a64 a32 aLast) :
    runInstructions (extraProgram slot t)
      (CiosCarryL1.state (carrySlot := carrySlot) template pc mem bi pa n j pbi pbEnd flag target2 inv
        (m0 :: tl :: a96 :: a64 :: a32 :: aLast :: dst :: ret :: rest)) =
    some (CiosCarryL1.state (carrySlot := carrySlot) template (pc+UInt256.ofNat 34) mem bi pa n (j+1)
      pbi pbEnd flag target2 inv (m0 :: tl :: a96 :: a64 :: a32 :: aLast :: dst :: ret :: rest)) := by
  let st : State := {template with memory := (l1Step mem bi pa n j).memory}
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat t.toNat 32) =
      st.activeWords := by
    rw [ht]
    exact activeWords_fix st _ 32 (by decide) (by omega) hactive
  have hvalue : cacheWord slot a96 a64 a32 =
      MachineState.readWord st.memory (pa+32*(n-1-j)) := by
    have h := (hc.l1 bi j hn hfour hpaFit).choose slot
    simpa only [st, ← hselect, hoff] using h
  have hl := run_extraLoad (carrySlot := carrySlot) slot st pc (l1Step mem bi pa n j).carry bi pbi
    (UInt256.ofNat pa) pbEnd flag target2 inv m0 tl a96 a64 a32 aLast dst ret rest hrest
  rw [hvalue] at hl
  let tail := [pbi,UInt256.ofNat pa,pbEnd,flag,carrySlot,allOnes,target2,inv,m0,tl,a96,a64,a32,aLast,dst,ret] ++ rest
  have htail : tail.length ≤ 1014 := by
    simp only [tail,List.length_append,List.length_cons,List.length_nil]; omega
  have hp := L2.run_product st (pc+UInt256.ofNat 2)
    (MachineState.readWord st.memory (pa+32*(n-1-j))) bi (l1Step mem bi pa n j).carry tail
    (by simp only [tail,List.length_append,List.length_cons,List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 18 (pc+UInt256.ofNat 2))
    (MachineState.readWord st.memory (pa+32*(n-1-j))) bi (l1Step mem bi pa n j).carry t t tail
    (by simp only [tail,List.length_append,List.length_cons,List.length_nil]; omega) hT hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 18 (pc+UInt256.ofNat 2)+UInt256.ofNat 14 = pc+UInt256.ofNat 34 := by
    simp [advancePC,succ_eq_add,word_add_assoc,Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [extraProgram, st, tail, CiosCarryL1.state, extendedStack, framed, l1Step, ht, hpc,
    List.cons_append,List.nil_append,List.append_assoc] using hall


open CiosCarryL1

def wideLoadProgram (off : UInt256) : List Instr :=
  [.push 5 off, .op (.Dup ⟨4, by decide⟩), .op .ADD,
   .op .MLOAD, .op (.Dup ⟨8, by decide⟩)]

def wideProgram (off t : UInt256) : List Instr :=
  (wideLoadProgram off ++ L2.productProgram) ++ L2.finishProgram t t

theorem wideProgram_eq (off t : UInt256) :
    wideProgram off t = (wideLoadProgram off ++ L2.productProgram) ++ L2.finishProgram t t := rfl

theorem run_wide_load (template : State)
    (pc off carry bi pbi paBase pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (paBase + off).toNat 32) = template.activeWords) :
    runInstructions (wideLoadProgram off)
      (framed template pc
        ([carry, bi, pbi, paBase, pbEnd, flag, carrySlot, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 10)
      ([maxWord, MachineState.readWord template.memory (paBase + off).toNat,
        carry, bi, pbi, paBase, pbEnd, flag, carrySlot, allOnes, destination, returnPC] ++ rest)) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp only [Challenge.EvmProof.Word.word_toNat_add,
    show (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      from by decide] at hactive
  simp [runInstructions, wideLoadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc10, hc11, hc12, State.activeWordsAfterUInt256, hactive, hN, succ_eq_add,
    word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_wide_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi : UInt256) (pa n j : Nat) (off t : UInt256)
    (hoff : off.toNat = 32 * (n - 1 - j))
    (ht : t.toNat = 8256 + 32 * (n - 1 - j))
    (pbi pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hj : j < n)
    (_hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    runInstructions (wideProgram off t)
      (state (carrySlot := carrySlot) template pc mem bi pa n j pbi pbEnd flag destination returnPC rest) =
    some (state (carrySlot := carrySlot) template (pc + UInt256.ofNat 42) mem bi pa n (j+1)
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
  have hl := run_wide_load (carrySlot := carrySlot) st pc off (l1Step mem bi pa n j).carry bi pbi (UInt256.ofNat pa)
    pbEnd flag destination returnPC rest hrest hA
  have hp := L2.run_product st (pc + UInt256.ofNat 10)
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (l1Step mem bi pa n j).carry
    ([pbi, UInt256.ofNat pa, pbEnd, flag, carrySlot, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf := L2.run_finish st (advancePC 18 (pc + UInt256.ofNat 10))
    (MachineState.readWord st.memory (UInt256.ofNat pa + off).toNat) bi
    (l1Step mem bi pa n j).carry t t
    ([pbi, UInt256.ofNat pa, pbEnd, flag, carrySlot, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hT
  have both := runInstructions_append_some _ _ _ _ _ hl hp
  have hall := runInstructions_append_some _ _ _ _ _ both hf
  have hpc : advancePC 18 (pc + UInt256.ofNat 10) + UInt256.ofNat 14 =
      pc + UInt256.ofNat 42 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [wideProgram_eq, st, state, framed, l1Step, haddr, ht, hpc,
    List.cons_append, List.nil_append] using hall




#print axioms run_step
#print axioms run_wide_step

end Challenge.Modexp.Submission.Proofs.Fast.CiosCarryOperand

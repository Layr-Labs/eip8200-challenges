import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true

/-!
Constant-address cached L2 cells. The two physical pointer words are inert;
the unchanged MONPRO recursion still determines each memory and carry step.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Const

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def loadProgram (p : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat p), .op .MLOAD, .op (.Dup ⟨11, by decide⟩)]

def accumulateLoadProgram (p : Nat) : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .push 2 (UInt256.ofNat (8256 + p)), .op .MLOAD]

def accumulateProgram (p : Nat) : List Instr :=
  accumulateLoadProgram p ++ CiosCachedMacCore.sumProgram

def tailProgram (p : Nat) : List Instr :=
  [.push 4 (UInt256.ofNat (8288 + p)), .op .MSTORE]

def program (p : Nat) : List Instr :=
  ((loadProgram p ++ CiosCachedMacCore.productProgram) ++ accumulateProgram p) ++ tailProgram p

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (32 * n - 64), UInt256.ofNat (8192 + 32 * n),
      (l2Step mem mu c0 n k).carry, mu, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }

/-- Keep literal word conversion out of the larger execution proofs. -/
private theorem address_toNat (p : Nat) (hp : p < 2^256) :
    (UInt256.ofNat p).toNat = p := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hp]

theorem run_load (p : Nat) (template : State)
    (pc pm pt carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) (hp : p < 2^256)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat p 32) = template.activeWords) :
    runInstructions (loadProgram p)
      (framed template pc
        ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([maxWord, MachineState.readWord template.memory p, pm, pt, carry, mu, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc12 : rest.length + 13 < 1024 := by omega
  have hc13 : rest.length + 14 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  have haddr := address_toNat p hp
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc12, hc13, State.activeWordsAfterUInt256, hactive, hN, haddr,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_accumulateLoad (p : Nat) (template : State) (pc part sum y pm pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) (hp : 8256 + p < 2^256)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (8256 + p) 32) = template.activeWords) :
    runInstructions (accumulateLoadProgram p)
      (framed template pc ([part, pm, pt, sum, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([MachineState.readWord template.memory (8256 + p), sum, part, pm, pt, sum, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have haddr := address_toNat (8256 + p) hp
  simp [runInstructions, accumulateLoadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc5, hc6, hc7, State.activeWordsAfterUInt256, hactive, haddr,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_accumulate (p : Nat) (template : State) (pc x y c pm pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) (hp : 8256 + p < 2^256)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (8256 + p) 32) = template.activeWords) :
    runInstructions (accumulateProgram p)
      (framed template pc ([partialCarry x y c, pm, pt, x * y + c, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 11)
      ([macSum x y (MachineState.readWord template.memory (8256 + p)) c, pm, pt,
        macCarry x y (MachineState.readWord template.memory (8256 + p)) c, y] ++ rest)) := by
  have hl := run_accumulateLoad p template pc (partialCarry x y c) (x*y+c) y pm pt
    rest hrest hp hactive
  have hs := CiosCachedMacCore.run_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory (8256 + p)) (x*y+c) (partialCarry x y c)
    y pm pt rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  rw [carry_eq, sum_eq] at both
  have hpc : advancePC 6 (pc + UInt256.ofNat 5) = pc + UInt256.ofNat 11 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [accumulateProgram, hpc] using both

theorem run_tail (p : Nat) (template : State)
    (pc pm pt sum carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) (hp : 8288 + p < 2^256)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (8288 + p) 32) = template.activeWords) :
    runInstructions (tailProgram p)
      (framed template pc
        ([sum, pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) (8288 + p) }
      (pc + UInt256.ofNat 6)
      ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc13 : rest.length + 14 < 1024 := by omega
  have hc14 : rest.length + 15 < 1024 := by omega
  have haddr := address_toNat (8288 + p) hp
  simp [runInstructions, tailProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc13, hc14, State.activeWordsAfterUInt256, hactive, haddr,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- Execute one fixed-address cell with arbitrary inert pointer words. -/
theorem run_words (p : Nat) (template : State)
    (pc pm pt carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) (hp : 8288 + p < 2^256)
    (hM : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat p 32) = template.activeWords)
    (hT : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (8256 + p) 32) = template.activeWords)
    (hW : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (8288 + p) 32) = template.activeWords) :
    runInstructions (program p)
      (framed template pc
        ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum (MachineState.readWord template.memory p) mu
              (MachineState.readWord template.memory (8256 + p)) carry).toNat 32) (8288 + p) }
      (pc + UInt256.ofNat 40)
      ([pm, pt,
        macCarry (MachineState.readWord template.memory p) mu
          (MachineState.readWord template.memory (8256 + p)) carry,
        mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hl := run_load p template pc pm pt carry mu bi
    pbi paEnd pbEnd flag destination returnPC rest hrest (by omega) hM
  have hm := CiosCachedMacCore.run_product template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory p) mu carry pm pt
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have ha := run_accumulate p template (advancePC 18 (pc + UInt256.ofNat 5))
    (MachineState.readWord template.memory p) mu carry pm pt
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by omega) hT
  have ht := run_tail p template (advancePC 18 (pc + UInt256.ofNat 5) + UInt256.ofNat 11) pm pt
    (macSum (MachineState.readWord template.memory p) mu
      (MachineState.readWord template.memory (8256 + p)) carry)
    (macCarry (MachineState.readWord template.memory p) mu
      (MachineState.readWord template.memory (8256 + p)) carry)
    mu bi pbi paEnd pbEnd flag destination returnPC rest hrest hp hW
  have first := runInstructions_append_some _ _ _ _ _ hl hm
  have both := runInstructions_append_some _ _ _ _ _ first ha
  have hall := runInstructions_append_some _ _ _ _ _ both ht
  have hpc : (advancePC 18 (pc + UInt256.ofNat 5) + UInt256.ofNat 11) + UInt256.ofNat 6 =
      pc + UInt256.ofNat 40 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program, hpc] using hall

/-- The logical recurrence advances while the physical pointer words stay fixed. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n) :
    runInstructions (program (32*(n-2-k)))
      (state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 40) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hwrite : 8288 + 32*(n-2-k) = 8256 + 32*(n-1-k) := by omega
  have hM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8288 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hall := run_words (32*(n-2-k)) st pc
    (UInt256.ofNat (32*n-64)) (UInt256.ofNat (8192 + 32*n))
    (l2Step mem mu c0 n k).carry mu bi pbi paEnd pbEnd flag destination returnPC rest
    hrest (by omega) hM hT hW
  simpa only [st, state, framed, l2Step, hwrite] using hall

/-- The smallest admitted width is the same fixed-address terminal cell. -/
theorem run_n2 (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) :
    runInstructions (program 0) (state template pc mem bi mu c0 2 0 pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 40) mem bi mu c0 2 1
      pbi paEnd pbEnd flag destination returnPC rest) :=
  run_step template pc mem bi mu c0 2 0 pbi paEnd pbEnd flag destination returnPC rest
    hrest hactive (by decide) (by decide)

theorem program_matches (p : Nat) : program p = CiosCached.l2ConstProgram p := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Const

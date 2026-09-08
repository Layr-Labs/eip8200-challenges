import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMac

set_option warningAsError true

/-!
Generic cached MAC execution against the unchanged MONPRO memory recursion.
No Artifact, concrete program counter, gas schedule or whole-candidate claim.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open MonproKNCache

def program : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
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
   .push 1 32,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (ptrAt (32*n - 64) k),
      UInt256.ofNat (ptrAt (8192 + 32*n) k),
      (l2Step mem mu c0 n k).carry, mu, bi, pbi, paEnd, pbEnd,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }


def loadProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨10, by decide⟩)]

def tailProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨11, by decide⟩), .op .ADD,
   .op (.Swap ⟨3, by decide⟩), .op .ADD, .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩), .op .ADD]

theorem program_eq :
    program = (loadProgram ++ MonproKNMac.program) ++ tailProgram := rfl

theorem run_load (template : State) (pc pm pt carry mu bi pbi paEnd pbEnd destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pm.toNat 32) = template.activeWords) :
    runInstructions loadProgram
      (framed template pc
        ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (advancePC 4 pc)
      ([maxWord, MachineState.readWord template.memory pm.toNat, pm, pt, carry, mu, bi,
        pbi, paEnd, pbEnd, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc12, hc13, State.activeWordsAfterUInt256, hactive, hN]

theorem run_tail (template : State) (pc pm pt sum carry mu bi pbi paEnd pbEnd destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (pt + UInt256.ofNat 32).toNat 32) = template.activeWords) :
    runInstructions tailProgram
      (framed template pc
        ([sum, pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) (pt + UInt256.ofNat 32).toNat }
      (advancePC 8 (pc + UInt256.ofNat 2))
      ([negative32 + pm, negative32 + pt, carry, mu, bi, pbi, paEnd, pbEnd,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [runInstructions, tailProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc12, hc13, hc14, hc15, hc16, h32, List.exchange,
    State.activeWordsAfterUInt256, hactive]

/-- Includes the n=2,k=0 final copy. The decremented modulus pointer may wrap. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n) :
    runInstructions program (state template pc mem bi mu c0 n k pbi paEnd pbEnd destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 41) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd destination returnPC rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hK : negative32 = UInt256.ofNat
      115792089237316195423570985008687907853269984665640564039457584007913129639904 :=
    negative32_value
  have hN : allOnes = maxWord := allOnes_value
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have hsize : (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936 := by decide
  have hpmj : ptrAt (32*n - 64) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32*(n-2-k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hptj : ptrAt (8192 + 32*n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32*(n-2-k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hwr : ptrAt (8224 + 32*n) k %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32*(n-1-k) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
  have hshift : 32 + ptrAt (8192 + 32*n) k = ptrAt (8224 + 32*n) k := by
    simp only [ptrAt]
    omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive

  have hwrite : (ptrAt (8192 + 32*n) k + 32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8256 + 32*(n-1-k) := by
    rw [Nat.add_comm (ptrAt (8192 + 32*n) k) 32, hshift, hwr]
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  let pm0 := UInt256.ofNat (ptrAt (32*n - 64) k)
  let pt0 := UInt256.ofNat (ptrAt (8192 + 32*n) k)
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat pm0.toNat 32) =
      st.activeWords := by
    simpa only [st, pm0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpmj] using hactM
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat pt0.toNat 32) =
      st.activeWords := by
    simpa only [st, pt0, Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hptj] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat
      (pt0 + UInt256.ofNat 32).toNat 32) = st.activeWords := by
    simpa only [st, pt0, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hwrite] using hactW
  have hl := run_load st pc pm0 pt0 (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd destination returnPC rest hrest hM
  have hm := MonproKNMac.run_mac st (advancePC 4 pc)
    (MachineState.readWord st.memory pm0.toNat) mu (l2Step mem mu c0 n k).carry pm0 pt0
    ([bi, pbi, paEnd, pbEnd, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have ht := run_tail st (advancePC 9 (advancePC 18 (advancePC 4 pc))) pm0 pt0
    (macSum (MachineState.readWord st.memory pm0.toNat) mu
      (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry)
    (macCarry (MachineState.readWord st.memory pm0.toNat) mu
      (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry)
    mu bi pbi paEnd pbEnd destination returnPC rest hrest hW
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both ht
  have hpc : advancePC 8 (advancePC 9 (advancePC 18 (advancePC 4 pc)) + UInt256.ofNat 2) =
      pc + UInt256.ofNat 41 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program_eq, st, pm0, pt0, state, framed, l2Step,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpmj, hptj, hwrite, hpc, hK,
    Challenge.EvmProof.Word.ofNat_add_mod, ptrAt_succ] using hall

/-- The smallest admitted multi-limb width needs exactly this one MAC. -/
theorem run_n2 (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi paEnd pbEnd destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1007)
    (hactive : 296 ≤ template.activeWords.toNat) :
    runInstructions program (state template pc mem bi mu c0 2 0 pbi paEnd pbEnd destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 41) mem bi mu c0 2 1
      pbi paEnd pbEnd destination returnPC rest) :=
  run_step template pc mem bi mu c0 2 0 pbi paEnd pbEnd destination returnPC rest
    hrest hactive (by decide) (by decide)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2

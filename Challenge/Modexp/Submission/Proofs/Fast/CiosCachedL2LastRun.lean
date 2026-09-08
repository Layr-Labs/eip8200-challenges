import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Last

set_option warningAsError true

/-! The last MAC preserves its dead pointer values while performing the same
memory recursion.  The public row tail accepts arbitrary discarded pointers. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2LastRun

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def program : List Instr :=
  (CiosCachedL2.loadProgram ++ CiosCachedMacCore.program) ++ CiosCachedL2Last.lastTail

def outputState (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [UInt256.ofNat (ptrAt (32*n - 64) k),
      UInt256.ofNat (ptrAt (8192 + 32*n) k),
      (l2Step mem mu c0 n (k+1)).carry, mu, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n (k+1)).memory }

theorem run_eq (ops : List Instr) (s : State) :
    CiosCachedL2Last.runProgram ops s = runInstructions ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      change (Challenge.EvmProof.Stepper.runInstr op s).bind (CiosCachedL2Last.runProgram ops) =
        (Challenge.EvmProof.Stepper.runInstr op s).bind (runInstructions ops)
      cases Challenge.EvmProof.Stepper.runInstr op s with
      | none => rfl
      | some next => exact ih next

theorem run_tail (template : State) (pc pm pt sum carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat (pt + UInt256.ofNat 32).toNat 32) = template.activeWords) :
    runInstructions CiosCachedL2Last.lastTail
      (framed template pc
        ([sum, pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) (pt + UInt256.ofNat 32).toNat }
      (advancePC 8 (pc + UInt256.ofNat 2))
      ([pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have h := CiosCachedL2Last.run_last template pc.toNat sum pm pt carry mu bi pbi
    paEnd pbEnd flag negative32 allOnes destination returnPC rest hrest hactive
  have hemb : UInt256.ofNat pc.toNat = pc :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat pc).symm
  have hpc : advancePC 8 (pc + UInt256.ofNat 2) = UInt256.ofNat (pc.toNat + 10) := by
    conv_lhs => rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat pc]
    simp [advancePC, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [run_eq, CiosCachedL2Last.input, CiosCachedL2Last.output,
    CiosCachedL2Last.stored, framed, hemb, ← hpc] using h

/-- All n=2..32 and k+1<n: memory/carry advance, pointers deliberately do not. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n) :
    runInstructions program (CiosCachedL2.state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (outputState template (pc + UInt256.ofNat 40) mem bi mu c0 n k
      pbi paEnd pbEnd flag destination returnPC rest) := by
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
  have hl := CiosCachedL2.run_load st pc pm0 pt0 (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hM
  have hm := CiosCachedMacCore.run_mac st (advancePC 3 pc)
    (MachineState.readWord st.memory pm0.toNat) mu (l2Step mem mu c0 n k).carry pm0 pt0
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have ht := run_tail st (advancePC 9 (advancePC 18 (advancePC 3 pc))) pm0 pt0
    (macSum (MachineState.readWord st.memory pm0.toNat) mu
      (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry)
    (macCarry (MachineState.readWord st.memory pm0.toNat) mu
      (MachineState.readWord st.memory pt0.toNat) (l2Step mem mu c0 n k).carry)
    mu bi pbi paEnd pbEnd flag destination returnPC rest hrest hW
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both ht
  have hpc : advancePC 8 (advancePC 9 (advancePC 18 (advancePC 3 pc)) + UInt256.ofNat 2) =
      pc + UInt256.ofNat 40 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program, st, pm0, pt0, CiosCachedL2.state, outputState, framed, l2Step,
    Challenge.EvmProof.Word.word_toNat_ofNat, hsize, hpmj, hptj, hwrite, hpc,
    Challenge.EvmProof.Word.ofNat_add_mod] using hall

/-- The smallest admitted multi-limb width needs exactly this one MAC. -/
theorem run_n2 (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) :
    runInstructions program (CiosCachedL2.state template pc mem bi mu c0 2 0 pbi paEnd pbEnd flag destination returnPC rest) =
    some (outputState template (pc + UInt256.ofNat 40) mem bi mu c0 2 0
      pbi paEnd pbEnd flag destination returnPC rest) :=
  run_step template pc mem bi mu c0 2 0 pbi paEnd pbEnd flag destination returnPC rest
    hrest hactive (by decide) (by decide)


theorem program_matches : program = CiosCached.l2LastProgram := rfl

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2LastRun

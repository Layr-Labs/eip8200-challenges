import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
Generic second-loop MAC execution against the unchanged MONPRO memory
recursion.  Every address is an immediate; no Artifact, concrete program
counter, gas schedule or whole-candidate claim.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast CiosCached CiosCachedMacCore

def state (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := [(l2Step mem mu c0 n k).carry, mu, bi, pbi, paEnd, pbEnd, flag,
      negative32, allOnes, destination, returnPC] ++ rest
    memory := (l2Step mem mu c0 n k).memory }

def loadProgram (x : UInt256) : List Instr :=
  [.push 2 x, .op .MLOAD,
   .op (.Dup ⟨9, by decide⟩)]

def storeProgram (ts : UInt256) : List Instr :=
  [.push 2 ts, .op .MSTORE]

theorem program_eq (x tl ts : UInt256) :
    l2Program x tl ts = (loadProgram x ++ L2.program tl) ++ storeProgram ts := rfl

theorem run_load (template : State) (pc x carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat x.toNat 32) = template.activeWords) :
    runInstructions (loadProgram x)
      (framed template pc
        ([carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([maxWord, MachineState.readWord template.memory x.toNat, carry, mu, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc11, hc12, State.activeWordsAfterUInt256, hactive, hN, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_store (template : State) (pc sum carry mu bi pbi paEnd pbEnd flag destination returnPC ts : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (storeProgram ts)
      (framed template pc
        ([sum, carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded sum.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 4)
      ([carry, mu, bi, pbi, paEnd, pbEnd, flag,
        negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [runInstructions, storeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc12, hc13, State.activeWordsAfterUInt256, hactive, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

/-- One second-loop copy; the immediates select limb `k` of an `n`-limb row. -/
theorem run_step (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x tl ts : UInt256)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 296 ≤ template.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n) :
    runInstructions (l2Program x tl ts) (state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat 38) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (8256 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat x.toNat 32) =
      st.activeWords := by
    simpa only [st, hx] using hactM
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by
    simpa only [st, htl] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat ts.toNat 32) =
      st.activeWords := by
    simpa only [st, hts] using hactW
  have hl := run_load st pc x (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hM
  have hm := L2.run_mac st (pc + UInt256.ofNat 5)
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry tl
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT
  have hs := run_store st (advancePC 6 (advancePC 18 (pc + UInt256.ofNat 5) + UInt256.ofNat 5))
    (macSum (MachineState.readWord st.memory x.toNat) mu
      (MachineState.readWord st.memory tl.toNat) (l2Step mem mu c0 n k).carry)
    (macCarry (MachineState.readWord st.memory x.toNat) mu
      (MachineState.readWord st.memory tl.toNat) (l2Step mem mu c0 n k).carry)
    mu bi pbi paEnd pbEnd flag destination returnPC ts rest hrest hW
  have both := runInstructions_append_some _ _ _ _ _ hl hm
  have hall := runInstructions_append_some _ _ _ _ _ both hs
  have hpc : advancePC 6 (advancePC 18 (pc + UInt256.ofNat 5) + UInt256.ofNat 5) + UInt256.ofNat 4 =
      pc + UInt256.ofNat 38 := by
    simp [advancePC, succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]
  simpa only [program_eq, st, state, framed, l2Step, hx, htl, hts, hpc] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFused

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

def loadProgram (w : Fin 33) (x : UInt256) : List Instr :=
  [.push w x, .op .MLOAD, .op (.Dup ⟨9, by decide⟩)]

theorem program_eq (w : Fin 33) (x tl ts : UInt256) :
    l2Program w x tl ts =
      loadProgram w x ++ macFusedProgram tl ts := rfl

theorem run_load (w : Fin 33)
    (template : State) (pc x carry mu bi pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hpush : w.val = 0 → x = UInt256.ofNat 0)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat x.toNat 32) = template.activeWords) :
    runInstructions (loadProgram w x)
      (framed template pc
        ([carry, mu, bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) =
    some (framed template (pc + UInt256.ofNat (w.val + 3))
      ([maxWord, MachineState.readWord template.memory x.toNat, carry, mu, bi,
        pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hN : allOnes = maxWord := allOnes_value
  by_cases hw : w.val = 0
  · have hx := hpush hw
    subst x
    have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
    change UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat 0 32) = template.activeWords at hactive
    simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hw, hc11, hc12, State.activeWordsAfterUInt256, hzero, hactive, hN, succ_eq_add,
      word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  · simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hw, hc11, hc12, State.activeWordsAfterUInt256, hactive, hN, succ_eq_add,
      word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]

/-- One second-loop copy. PUSH0 is admitted only for an actual zero address. -/
theorem run_step (w : Fin 33) (template : State) (pc : UInt256) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat) (x tl ts : UInt256)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 2112 + 32 * (n - 2 - k))
    (hts : ts.toNat = 2112 + 32 * (n - 1 - k))
    (pbi paEnd pbEnd flag destination returnPC : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : 91 ≤ template.activeWords.toNat) (hn : n ≤ 8) (hk : k+1 < n)
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    runInstructions (l2Program w x tl ts)
      (state template pc mem bi mu c0 n k pbi paEnd pbEnd flag destination returnPC rest) =
    some (state template (pc + UInt256.ofNat (w.val + 35)) mem bi mu c0 n (k+1)
      pbi paEnd pbEnd flag destination returnPC rest) := by
  have hactM : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-2-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  have hactW : UInt256.ofNat (MachineState.activeWordsAfter template.activeWords.toNat
      (2112 + 32*(n-1-k)) 32) = template.activeWords :=
    activeWords_fix template _ 32 (by decide) (by omega) hactive
  let st : State := { template with memory := (l2Step mem mu c0 n k).memory }
  have hM : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat x.toNat 32) =
      st.activeWords := by simpa only [st, hx] using hactM
  have hT : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat tl.toNat 32) =
      st.activeWords := by simpa only [st, htl] using hactT
  have hW : UInt256.ofNat (MachineState.activeWordsAfter st.activeWords.toNat ts.toNat 32) =
      st.activeWords := by simpa only [st, hts] using hactW
  have hl := run_load w st pc x (l2Step mem mu c0 n k).carry mu bi
    pbi paEnd pbEnd flag destination returnPC rest hrest hpush hM
  have hf := CiosCachedFused.run_fused st (pc + UInt256.ofNat (w.val + 3))
    (MachineState.readWord st.memory x.toNat) mu (l2Step mem mu c0 n k).carry tl ts
    ([bi, pbi, paEnd, pbEnd, flag, negative32, allOnes, destination, returnPC] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hT hW
  have hall := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : (pc + UInt256.ofNat (w.val + 3)) + UInt256.ofNat 32 =
      pc + UInt256.ofNat (w.val + 35) := by
    simp [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc]
  simpa only [program_eq, st, state, framed, l2Step, hx, htl, hts, hpc,
    List.cons_append, List.nil_append] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2

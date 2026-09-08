import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpread
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Located packed spread preprocessing

This module composes the frozen `PUSH4 mask; sixteen descending groups; POP`
artifact span.  Its memory postcondition is the already-proved
`PackedPreprocessLayout.spreadMemory`; it does not make a whole-word
disjointness assumption about the overlapping source loads.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpreadSite

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open StackRoundTemplate
open PackedPreprocessLayout
open PackedPreprocessSpread

abbrev A := Artifact.submissionArtifact

def spreadGroupsTemplate (n : Nat) : List Instr :=
  (List.range n).reverse.flatMap spreadStoreTemplate

@[simp] theorem spreadGroupsTemplate_zero : spreadGroupsTemplate 0 = [] := by
  rfl

theorem spreadGroupsTemplate_succ (n : Nat) :
    spreadGroupsTemplate (n + 1) =
      spreadStoreTemplate n ++ spreadGroupsTemplate n := by
  simp [spreadGroupsTemplate, List.range_succ]

theorem pcAfter_append (pc : UInt256) (first second : List Instr) :
    PackedPreprocessSpread.pcAfter pc (first ++ second) =
      PackedPreprocessSpread.pcAfter
        (PackedPreprocessSpread.pcAfter pc first) second := by
  induction first generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.cons_append, PackedPreprocessSpread.pcAfter]
      exact ih (pc := pc + UInt256.ofNat instruction.size)

theorem runInstrSeq_append_running
    {first second : List Instr} {s middle result : State}
    (hfirst : PackedPreprocessSpread.runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running)
    (hsecond : PackedPreprocessSpread.runInstrSeq second middle = some result) :
    PackedPreprocessSpread.runInstrSeq (first ++ second) s = some result := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, PackedPreprocessSpread.runInstrSeq] at hfirst ⊢
      cases hfirst
      exact hsecond
  | cons instruction rest ih =>
      cases hrun : Stepper.runInstr instruction s with
      | none =>
          simp [PackedPreprocessSpread.runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [PackedPreprocessSpread.runInstrSeq, hrun] using hfirst
              subst middle
              cases second with
              | nil =>
                  simpa [PackedPreprocessSpread.runInstrSeq, hrun] using hsecond
              | cons nextInstruction secondRest =>
                  simpa [PackedPreprocessSpread.runInstrSeq, hrun, hmiddle]
                    using hsecond
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have htail : PackedPreprocessSpread.runInstrSeq
                      (nextInstruction :: restTail) next = some middle := by
                    simpa [PackedPreprocessSpread.runInstrSeq, hrun, hhalt]
                      using hfirst
                  have hjoined := ih (s := next) (middle := middle)
                    htail hmiddle hsecond
                  simpa [PackedPreprocessSpread.runInstrSeq, hrun, hhalt]
                    using hjoined
              | Success =>
                  simp [PackedPreprocessSpread.runInstrSeq, hrun, hhalt] at hfirst
              | Returned =>
                  simp [PackedPreprocessSpread.runInstrSeq, hrun, hhalt] at hfirst
              | Reverted =>
                  simp [PackedPreprocessSpread.runInstrSeq, hrun, hhalt] at hfirst
              | Exception error =>
                  simp [PackedPreprocessSpread.runInstrSeq, hrun, hhalt] at hfirst

def spreadStep (s : State) (n : Nat) : State :=
  { s with
    memory := PackedGapInvariant.storeWord s.memory (destinationAddress n)
      (spreadValue s.memory n) }

def spreadGroupsReturned (s : State) (endPC : UInt256) (n : Nat)
    (rest : List UInt256) : State :=
  { s with
    pc := endPC
    stack := UInt256.ofNat mask32 :: rest
    memory := runtimeSpread n s.memory }

theorem spreadStoreReturned_eq_entry_step (s : State) (endPC : UInt256)
    (n : Nat) (rest : List UInt256) (hn : n < 16)
    (hactive : 11 ≤ s.activeWords.toNat) :
    spreadStoreReturned s endPC n rest =
      spreadStoreEntry (spreadStep s n) endPC rest := by
  simp [spreadStoreReturned, spreadStoreEntry, spreadStep,
    spreadActiveWords_eq s n hn hactive]

@[simp] theorem spreadStep_halt (s : State) (n : Nat) :
    (spreadStep s n).halt = s.halt := by
  rfl

@[simp] theorem spreadStep_activeWords (s : State) (n : Nat) :
    (spreadStep s n).activeWords = s.activeWords := by
  rfl

theorem runInstrSeq_spreadGroups (s : State) (startPC : UInt256) (n : Nat)
    (rest : List UInt256) (hn : n ≤ 16)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    PackedPreprocessSpread.runInstrSeq (spreadGroupsTemplate n)
        (spreadStoreEntry s startPC rest) =
      some (spreadGroupsReturned s
        (PackedPreprocessSpread.pcAfter startPC (spreadGroupsTemplate n))
        n rest) := by
  induction n generalizing s startPC with
  | zero =>
      rfl
  | succ n ih =>
      have hn16 : n < 16 := by omega
      let middlePC := PackedPreprocessSpread.pcAfter startPC
        (spreadStoreTemplate n)
      let middle := spreadStoreEntry (spreadStep s n) middlePC rest
      have hfirst : PackedPreprocessSpread.runInstrSeq (spreadStoreTemplate n)
          (spreadStoreEntry s startPC rest) = some middle := by
        rw [runInstrSeq_spreadStore s startPC n rest hn16 hstack hrun]
        exact congrArg some
          (spreadStoreReturned_eq_entry_step s middlePC n rest hn16 hactive)
      have hmiddleRunning : middle.halt = .Running := by
        change s.halt = .Running
        exact hrun
      have htail : PackedPreprocessSpread.runInstrSeq (spreadGroupsTemplate n)
          middle =
        some (spreadGroupsReturned (spreadStep s n)
          (PackedPreprocessSpread.pcAfter middlePC (spreadGroupsTemplate n))
          n rest) := by
        exact ih (s := spreadStep s n) (startPC := middlePC) (by omega)
          (by simpa using hactive) (by simpa using hrun)
      have hjoined := runInstrSeq_append_running hfirst hmiddleRunning htail
      rw [spreadGroupsTemplate_succ]
      simpa [middlePC, middle, spreadGroupsReturned, spreadStep, runtimeSpread,
        pcAfter_append]
        using hjoined

def spreadEntry (s : State) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 635, stack := rest }

def spreadReturned (s : State) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 784
    stack := rest
    memory := spreadMemory s.memory }

private theorem spreadGroups_endPC :
    PackedPreprocessSpread.pcAfter (UInt256.ofNat 640)
      (spreadGroupsTemplate 16) = UInt256.ofNat 783 := by
  decide

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_spreadTemplate (s : State) (rest : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    PackedPreprocessSpread.runInstrSeq spreadTemplate (spreadEntry s rest) =
      some (spreadReturned s rest) := by
  have h0 : rest.length < 1024 := by omega
  have hpc640 :
      UInt256.ofNat 635 + UInt256.ofNat 5 = UInt256.ofNat 640 := by
    decide
  have hprefix : PackedPreprocessSpread.runInstrSeq
      [PackedPreprocessLayout.push4 mask32] (spreadEntry s rest) =
      some (spreadStoreEntry s (UInt256.ofNat 640) rest) := by
    simp [PackedPreprocessSpread.runInstrSeq, spreadEntry, spreadStoreEntry,
      PackedPreprocessLayout.push4, mask32, Stepper.runInstr, hrun, h0,
      Challenge.EvmProof.Word.succ_ofNat_mod, hpc640]
  have hgroups := runInstrSeq_spreadGroups s (UInt256.ofNat 640) 16 rest
    (Nat.le_refl 16) hactive hstack hrun
  rw [spreadGroups_endPC] at hgroups
  have hgroupsRunning :
      (spreadGroupsReturned s (UInt256.ofNat 783) 16 rest).halt = .Running := by
    simpa [spreadGroupsReturned] using hrun
  have hpopCap : rest.length + 1 < 1024 := by omega
  have hpc784 : (UInt256.ofNat 783).succ = UInt256.ofNat 784 := by
    decide
  have hpop : PackedPreprocessSpread.runInstrSeq [PackedPreprocessLayout.op .POP]
      (spreadGroupsReturned s (UInt256.ofNat 783) 16 rest) =
      some (spreadReturned s rest) := by
    simp [PackedPreprocessSpread.runInstrSeq, spreadGroupsReturned,
      spreadReturned, PackedPreprocessLayout.op, Stepper.runInstr, hrun,
      hpopCap, hpc784, runtimeSpread_full]
  have hfirst := runInstrSeq_append_running hprefix hrun hgroups
  have hall := runInstrSeq_append_running hfirst hgroupsRunning hpop
  simpa [spreadTemplate, spreadGroupsTemplate] using hall

theorem local_runInstrSeq_eq_round_runInstrSeq (instructions : List Instr)
    (s : State) :
    PackedPreprocessSpread.runInstrSeq instructions s =
      StackRoundTrace.runInstrSeq instructions s := by
  induction instructions generalizing s with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [PackedPreprocessSpread.runInstrSeq,
        StackRoundTrace.runInstrSeq]
      cases hstep : Stepper.runInstr instruction s with
      | none => rfl
      | some next =>
          cases rest with
          | nil => rfl
          | cons nextInstruction tail =>
              simp only
              cases next.halt <;> try rfl
              exact ih next

private theorem runInstr_pc_mstore {s t : State}
    (hresult : Stepper.runInstr (.op .MSTORE) s = some t) :
    t.pc = s.pc + UInt256.ofNat (Instr.op .MSTORE).size := by
  by_cases hcap : s.stack.length < 1024
  · rw [Stepper.runInstr, if_pos hcap] at hresult
    cases hs : s.stack with
    | nil => simp [hs] at hresult
    | cons address tail =>
        cases ht : tail with
        | nil => simp [hs, ht] at hresult
        | cons value rest =>
            simp [hs, ht] at hresult
            subst t
            rfl
  · simp [Stepper.runInstr, hcap] at hresult

private theorem spreadStoreTemplate_advances (n : Nat) :
    ∀ instruction ∈ spreadStoreTemplate n, ∀ {s t : State},
      Stepper.runInstr instruction s = some t →
        t.pc = s.pc + UInt256.ofNat instruction.size := by
  intro instruction hmem s t hresult
  simp only [spreadStoreTemplate, List.mem_cons, List.not_mem_nil, or_false]
    at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · by_cases hn0 : n = 0
    · simp only [destinationPush, if_pos hn0] at hresult ⊢
      exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
    · simp only [destinationPush, if_neg hn0] at hresult ⊢
      exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · exact runInstr_pc_mstore hresult

private theorem spreadTemplate_advances :
    ∀ instruction ∈ spreadTemplate, ∀ {s t : State},
      Stepper.runInstr instruction s = some t →
        t.pc = s.pc + UInt256.ofNat instruction.size := by
  intro instruction hmem s t hresult
  simp only [spreadTemplate, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with (rfl | hgroups) | rfl
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult
  · rw [List.mem_flatMap] at hgroups
    rcases hgroups with ⟨n, _, hn⟩
    exact spreadStoreTemplate_advances n instruction hn hresult
  · exact StackRoundTrace.runInstr_pc_of_straight (by constructor) hresult

theorem code_bound : A.code.size < UInt256.size := by
  change submissionBytecode.size < UInt256.size
  rw [referenceBytecode_size]
  decide

private theorem spreadTemplate_wellFormed : ∀ instruction ∈ spreadTemplate,
    Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by decide)

def spreadSite : GenericRoundSite A .Osaka spreadTemplate :=
  StackSiteBuilder.ofSlice spreadTemplate 362 artifact_spread_slice (by
    change 362 + spreadTemplate.length ≤ Artifact.submissionInstructions.length
    rw [spreadTemplate_length, Artifact.referenceInstructions_count]
    decide) code_bound spreadTemplate_wellFormed (by decide)

@[simp] theorem spreadSite_startPC :
    spreadSite.startPC = UInt256.ofNat 635 := by
  rfl

@[simp] theorem spreadSite_endPC :
    spreadSite.endPC = UInt256.ofNat 784 := by
  rfl

theorem runLocatedBlock_spread (s : State) (rest : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock spreadSite.path (spreadEntry s rest) =
      some (spreadReturned s rest) := by
  have hraw := StackRoundTrace.runLocatedBlock_eq_runInstrSeq_site
    spreadSite (spreadEntry s rest) rfl (by
      intro located hmem u v hresult
      apply spreadTemplate_advances located.located.instruction ?_ hresult
      rw [← spreadSite.instruction_eq]
      exact List.mem_map_of_mem hmem)
  rw [← local_runInstrSeq_eq_round_runInstrSeq] at hraw
  rw [hraw]
  exact runInstrSeq_spreadTemplate s rest hactive hstack hrun

def gasSteps_spread (s : State) (rest : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (spreadEntry s rest) (spreadReturned s rest) := by
  have hartifactCode : s.executionEnv.code = A.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  apply Stepper.runLocatedBlock_sound A .Osaka spreadSite.path
  · simpa [spreadEntry] using hartifactCode
  · simpa [spreadEntry] using hfork
  · exact runLocatedBlock_spread s rest hactive hstack hrun
  · simpa [spreadEntry] using hrun
  · simpa [spreadEntry] using hnp

#print axioms runInstrSeq_spreadGroups
#print axioms runInstrSeq_spreadTemplate
#print axioms gasSteps_spread

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpreadSite

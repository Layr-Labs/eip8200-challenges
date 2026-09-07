import Challenge.Ripemd160.Submission.Proofs.Bytecode.ConstpropQuad

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityPCTransport

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

theorem runInstr_relocate_straight {instruction : Instr}
    (hform : StraightLine instruction) (s : State) (pc : UInt256) :
    Stepper.runInstr instruction {s with pc := pc} =
      Option.map (fun t => {t with pc := pc + UInt256.ofNat instruction.size})
        (Stepper.runInstr instruction s) := by
  cases hform <;> unfold Stepper.runInstr <;> split
  all_goals simp_all only
  all_goals repeat' first | split | simp_all
  all_goals first | rfl | simp [Nat.add_comm, State.activeWordsAfterUInt256]
  all_goals rfl

theorem runInstr_relocate {instruction : Instr}
    (hform : PairMultiplyLift.Advances instruction) (s : State) (pc : UInt256) :
    Stepper.runInstr instruction {s with pc := pc} =
      Option.map (fun t => {t with pc := pc + UInt256.ofNat instruction.size})
        (Stepper.runInstr instruction s) := by
  rcases hform with (hstraight | hsub | hjumpdest) | hmul
  · exact runInstr_relocate_straight hstraight s pc
  all_goals subst instruction
  all_goals unfold Stepper.runInstr; split
  all_goals repeat' first | split | simp_all
  all_goals rfl

/-- Moving a pure instruction sequence changes only its final PC. No memory,
stack, arithmetic, code, or environmental field is abstracted away. -/
theorem runInstrSeq_relocate (code : List Instr)
    (hform : ∀ instruction ∈ code, PairMultiplyLift.Advances instruction)
    (s : State) (pc : UInt256) :
    runInstrSeq code {s with pc := pc} =
      Option.map (fun t => {t with pc := pcAfter pc code}) (runInstrSeq code s) := by
  induction code generalizing s pc with
  | nil => rfl
  | cons instruction rest ih =>
      have hfirst := runInstr_relocate (hform instruction (by simp)) s pc
      have hrest : ∀ i ∈ rest, PairMultiplyLift.Advances i := by
        intro i hi
        exact hform i (by simp [hi])
      cases hstep : Stepper.runInstr instruction s with
      | none =>
          simp [runInstrSeq, hfirst, hstep]
      | some next =>
          cases rest with
          | nil => simp [runInstrSeq, hfirst, hstep, pcAfter]
          | cons second tail =>
              cases hhalt : next.halt <;>
                simp [runInstrSeq, hfirst, hstep, hhalt, pcAfter]
              simpa only [runInstrSeq, pcAfter, hhalt] using
                ih hrest next (pc + UInt256.ofNat instruction.size)

theorem runInstr_preserves_halt {instruction : Instr}
    (hform : PairMultiplyLift.Advances instruction) {s t : State}
    (hresult : Stepper.runInstr instruction s = some t) : t.halt = s.halt := by
  rcases hform with (hstraight | hsub | hjumpdest) | hmul
  · cases hstraight <;> unfold Stepper.runInstr at hresult
    all_goals repeat' first | split at hresult | simp_all
    all_goals subst t; rfl
  all_goals subst instruction; unfold Stepper.runInstr at hresult
  all_goals repeat' first | split at hresult | simp_all
  all_goals subst t; rfl

/-- Recover the intermediate state at an arbitrary split, without evaluating
the arithmetic prefix. Combined with relocation this certifies cavity seams. -/
theorem runInstrSeq_split (first second : List Instr)
    (hform : ∀ instruction ∈ first, PairMultiplyLift.Advances instruction)
    {s t : State} (hrun : s.halt = .Running)
    (hwhole : runInstrSeq (first ++ second) s = some t) :
    ∃ middle, runInstrSeq first s = some middle ∧
      middle.halt = .Running ∧ runInstrSeq second middle = some t := by
  induction first generalizing s with
  | nil => exact ⟨s, rfl, hrun, hwhole⟩
  | cons instruction rest ih =>
      have hi := hform instruction (by simp)
      have hrest : ∀ i ∈ rest, PairMultiplyLift.Advances i := by
        intro i himem
        exact hform i (by simp [himem])
      cases hstep : Stepper.runInstr instruction s with
      | none => simp [runInstrSeq, hstep] at hwhole
      | some next =>
          have hnext : next.halt = .Running :=
            (runInstr_preserves_halt hi hstep).trans hrun
          have htail : runInstrSeq (rest ++ second) next = some t := by
            cases hlist : rest ++ second with
            | nil =>
                simpa only [List.cons_append, hlist, runInstrSeq, hstep] using hwhole
            | cons a tail =>
                simpa only [List.cons_append, hlist, runInstrSeq, hstep, hnext] using hwhole
          obtain ⟨middle, hprefix, hmiddle, hsuffix⟩ := ih hrest hnext htail
          refine ⟨middle, ?_, hmiddle, hsuffix⟩
          cases rest <;> simpa only [runInstrSeq, hstep, hnext] using hprefix

#print axioms runInstr_relocate_straight
#print axioms runInstr_relocate
#print axioms runInstrSeq_relocate
#print axioms runInstr_preserves_halt
#print axioms runInstrSeq_split

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityPCTransport

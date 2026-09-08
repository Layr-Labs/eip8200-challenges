import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedInvariants

set_option warningAsError true
set_option autoImplicit false

/-!
# Active-memory monotonicity for packed located blocks

The packed round opcode subset contains no store or call.  Its only operation
that changes `activeWords` is `MLOAD`, whose EVM update takes the maximum of
the incoming high-water mark and the loaded range.  These lemmas retain that
fact through an exact `LocatedPlan`; they do not infer it from the abstract
stack evaluator or from an arbitrary `GasSteps` witness.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedActiveWords

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedRunOpBridge PackedStep0

private theorem activeWordsAfter_ge (curr offset size : Nat) :
    curr ≤ MachineState.activeWordsAfter curr offset size := by
  rw [MachineState.activeWordsAfter]
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

private theorem activeWordsAfter32_lt (curr offset : UInt256) :
    MachineState.activeWordsAfter curr.toNat offset.toNat 32 < 2 ^ 256 := by
  have hcurr : curr.toNat < 2 ^ 256 := curr.val.isLt
  have hoffset : offset.toNat < 2 ^ 256 := offset.val.isLt
  rw [MachineState.activeWordsAfter]
  split
  · exact hcurr
  · rw [Nat.max_lt]
    constructor
    · exact hcurr
    · have hdiv : (offset.toNat + 32 - 1) / 32 < 2 ^ 256 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        omega
      omega

/-- A concrete 32-byte memory access cannot lower the active-memory extent.
The range result is proved below the UInt256 modulus before rewriting
`UInt256.ofNat`; no wraparound premise is hidden. -/
theorem activeWordsAfterUInt256_mload_ge (s : State) (offset : UInt256) :
    s.activeWords.toNat ≤
      (s.activeWordsAfterUInt256 offset.toNat 32).toNat := by
  rw [State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter32_lt s.activeWords offset)]
  exact activeWordsAfter_ge _ _ _

/-- Every successful concrete instruction represented by the packed model
preserves or increases `activeWords`.  The exact encoding premise excludes
unmodelled opcodes; the stack cap is the real global guard in `runInstr`. -/
theorem instruction_activeWords_mono {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    s.activeWords.toNat ≤ next.activeWords.toNat := by
  cases encoding.shape with
  | mload =>
      unfold Stepper.runInstr at hstep
      rw [if_pos hcap] at hstep
      cases hstack : s.stack with
      | nil => simp [hstack] at hstep
      | cons offset rest =>
          rw [hstack] at hstep
          injection hstep with hnext
          subst next
          exact activeWordsAfterUInt256_mload_ge s offset
  | push0 | push | dup | swap | pop | land | lor | xor | add | mul | shr =>
      unfold Stepper.runInstr at hstep
      rw [if_pos hcap] at hstep
      repeat' first | split at hstep | simp_all
      all_goals (subst next; exact Nat.le_refl _)

/-- Monotonicity composes over a successful exact located block. -/
theorem block_activeWords_mono {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)} {s t : State}
    (plan : LocatedPlan ops path s) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hresult : Stepper.runLocatedBlock path s = some t) :
    s.activeWords.toNat ≤ t.activeWords.toNat := by
  induction ops generalizing path s with
  | nil =>
      cases path with
      | nil =>
          simp only [Stepper.runLocatedBlock, Option.some.injEq] at hresult
          subst t
          exact Nat.le_refl _
      | cons located tail => simp [LocatedPlan] at plan
  | cons op ops ih =>
      cases path with
      | nil => simp [LocatedPlan] at plan
      | cons located tail =>
          rcases plan with ⟨shape, hcap, hpc, htail⟩
          let encoding : EncodesOp s.fork op located.instruction :=
            ⟨shape, by simpa [hfork] using located.wellFormed⟩
          cases hstep : Stepper.runInstr located.instruction s with
          | none =>
              simp [Stepper.runLocatedBlock, Stepper.runLocated, hpc, hstep]
                at hresult
          | some next =>
              have hhead := instruction_activeWords_mono encoding hcap hstep
              have hnextRun : next.halt = .Running :=
                (runInstr_halt_of_encoding encoding hcap hstep).trans hrun
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [Stepper.runInstr_executionEnv hstep]
                exact hfork
              cases tail with
              | nil =>
                  simp only [Stepper.runLocatedBlock, Stepper.runLocated,
                    if_pos hpc, hstep, Option.some.injEq] at hresult
                  subst t
                  exact hhead
              | cons following rest =>
                  have hrest :
                      Stepper.runLocatedBlock (following :: rest) next = some t := by
                    simpa only [Stepper.runLocatedBlock, Stepper.runLocated,
                      if_pos hpc, hstep, hnextRun] using hresult
                  exact hhead.trans
                    (ih (htail next hstep) hnextFork hnextRun hrest)

#print axioms activeWordsAfterUInt256_mload_ge
#print axioms instruction_activeWords_mono
#print axioms block_activeWords_mono

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedActiveWords

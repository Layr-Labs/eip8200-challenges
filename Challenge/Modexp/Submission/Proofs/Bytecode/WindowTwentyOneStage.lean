import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

/-!
Artifact-independent staged-modulus execution for the twenty-one-nibble route.
Concrete bytecode bindings are supplied separately.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

def stageProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩)]

def pairProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def fourSquaresProgram : List Instr :=
  pairProgram ++ pairProgram ++ pairProgram ++ pairProgram

private theorem run_dupTop (template : State) (pc value : UInt256)
    (tail : List UInt256) (hcap : tail.length + 1 < 1024) :
    runInstructions [.op (.Dup ⟨0, by decide⟩)]
      (framed template pc (value :: tail)) =
    some (framed template pc.succ (value :: value :: tail)) := by
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap]

/-- Repeated top duplication, with a normalized state boundary after every step. -/
theorem run_topCopies (template : State) (pc value : UInt256)
    (tail : List UInt256) (count : Nat) :
    tail.length + count + 1 < 1024 →
    runInstructions (List.replicate count (.op (.Dup ⟨0, by decide⟩)))
      (framed template pc (value :: tail)) =
    some (framed template (advancePC count pc)
      (List.replicate (count + 1) value ++ tail)) := by
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro hcap
      have before := ih (by omega)
      have after := run_dupTop template (advancePC count pc) value
        (List.replicate count value ++ tail)
        (by simp only [List.length_append, List.length_replicate]; omega)
      have after' :
          runInstructions [.op (.Dup ⟨0, by decide⟩)]
            (framed template (advancePC count pc)
              (List.replicate (count + 1) value ++ tail)) =
          some (framed template (advancePC (count + 1) pc)
            (List.replicate (count + 1 + 1) value ++ tail)) := by
        simpa only [List.replicate_succ, List.cons_append, advancePC] using after
      have both := runInstructions_append_some _ _ _ _ _ before after'
      simpa only [← List.replicate_succ'] using both

private theorem run_liftModulus (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Dup ⟨1, by decide⟩)]
      (framed template pc ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (framed template pc.succ
      ([modulus, accumulator, modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 5 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap, Nat.add_assoc]

private theorem run_swap15 (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Swap ⟨14, by decide⟩)]
      (framed template pc (List.replicate 15 modulus ++
        [accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (framed template pc.succ
      ((accumulator :: List.replicate 15 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 20 < 1024 := by omega
  simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap, Nat.add_assoc, List.replicate, List.exchange]

/-- Fifteen staged modulus copies. The following DUP reaches local height 21. -/
theorem run_stage (template : State) (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stageProgram
      (framed template pc ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (framed template (advancePC 16 pc)
      ((accumulator :: List.replicate 15 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have h0 := run_liftModulus template pc accumulator modulus exponent mask counter rest hrest
  have h1 := run_topCopies template pc.succ modulus
    ([accumulator, modulus, exponent, mask, counter] ++ rest) 14
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_swap15 template (advancePC 14 pc.succ)
    accumulator modulus exponent mask counter rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  have hpc : (advancePC 14 pc.succ).succ = advancePC 16 pc := rfl
  simpa only [stageProgram, hpc, List.replicate, List.cons_append, List.nil_append] using hall

private theorem run_pair (template : State) (pc accumulator modulus : UInt256)
    (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructions pairProgram
      (framed template pc (accumulator :: modulus :: tail)) =
    some (framed template (advancePC 2 pc)
      (UInt256.mulMod accumulator accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  simp (disch := omega)
    [runInstructions, pairProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap, hcap2, List.getElem?_cons_zero, advancePC]

/-- Consume four copies without changing the remaining frame or memory. -/
theorem run_fourSquares (template : State) (pc accumulator modulus : UInt256)
    (tail : List UInt256) (hcap : tail.length + 6 < 1024) :
    runInstructions fourSquaresProgram
      (framed template pc ([accumulator, modulus, modulus, modulus, modulus] ++ tail)) =
    some (framed template (advancePC 8 pc)
      (WindowMath.squareWordAfter modulus 4 accumulator :: tail)) := by
  let a1 := UInt256.mulMod accumulator accumulator modulus
  let a2 := UInt256.mulMod a1 a1 modulus
  let a3 := UInt256.mulMod a2 a2 modulus
  have h1 := run_pair template pc accumulator modulus
    ([modulus, modulus, modulus] ++ tail) (by simpa using hcap)
  have h2 := run_pair template (advancePC 2 pc) a1 modulus
    ([modulus, modulus] ++ tail) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h3 := run_pair template (advancePC 2 (advancePC 2 pc)) a2 modulus
    (modulus :: tail) (by simp only [List.length_cons]; omega)
  have h4 := run_pair template (advancePC 2 (advancePC 2 (advancePC 2 pc))) a3 modulus
    tail (by omega)
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have hall := runInstructions_append_some _ _ _ _ _ h123 h4
  simpa only [fourSquaresProgram, a1, a2, a3, WindowMath.squareWordAfter,
    ← advancePC_add, show 2 + 2 + 2 + 2 = 8 by decide,
    List.cons_append, List.nil_append] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage

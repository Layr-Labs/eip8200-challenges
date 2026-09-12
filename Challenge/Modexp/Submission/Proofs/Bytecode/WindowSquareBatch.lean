import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowSquareBatch

def stage6 : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨8, by decide⟩)]
def stage5 : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩)]
def stage4 : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩)]
def pair : List Instr := [.op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

set_option linter.unusedSimpArgs false in
private theorem run_pair (template : State) (pc accumulator modulus : UInt256)
    (tail : List UInt256) (hcap : tail.length + 3 < 1024) :
    runInstructions pair (framed template pc (accumulator :: modulus :: tail)) =
    some (framed template (advancePC 2 pc)
      (UInt256.mulMod accumulator accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, pair, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap, hcap2, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.exchange, advancePC]

def program6 : List Instr := stage6 ++ pair ++ pair ++ pair ++ pair

def program5 : List Instr := stage5 ++ pair ++ pair ++ pair ++ pair

def program4 : List Instr := stage4 ++ pair ++ pair ++ pair ++ pair

set_option linter.unusedSimpArgs false in
private theorem run_stage6 (template : State) (pc x0 x1 x2 x3 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stage6
      (framed template pc ([x0,x1,x2,x3,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 5 pc)
      ([accumulator,modulus,modulus,modulus,modulus] ++
        [x0,x1,x2,x3,accumulator,modulus] ++ rest)) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, stage6, framed, Challenge.EvmProof.Stepper.runInstr,
      hrest, h6, h7, h8, h9, h10, h11,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

theorem run_batch6 (template : State) (pc x0 x1 x2 x3 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program6
      (framed template pc ([x0,x1,x2,x3,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 13 pc)
      (WindowMath.squareWordAfter modulus 4 accumulator ::
        [x0,x1,x2,x3,accumulator,modulus] ++ rest)) := by
  let initial := [x0,x1,x2,x3,accumulator,modulus] ++ rest
  let a1 := UInt256.mulMod accumulator accumulator modulus
  let a2 := UInt256.mulMod a1 a1 modulus
  let a3 := UInt256.mulMod a2 a2 modulus
  have h0 := run_stage6 template pc x0 x1 x2 x3 accumulator modulus rest hrest
  have h1 := run_pair template (advancePC 5 pc) accumulator modulus
    ([modulus,modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_pair template (advancePC 2 (advancePC 5 pc)) a1 modulus
    ([modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h3 := run_pair template (advancePC 2 (advancePC 2 (advancePC 5 pc))) a2 modulus
    (modulus :: initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h4 := run_pair template (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 5 pc)))) a3 modulus
    initial (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  have hall := runInstructions_append_some _ _ _ _ _ h0123 h4
  simpa only [program6, initial, a1, a2, a3, WindowMath.squareWordAfter,
    ← advancePC_add, show 5 + 2 + 2 + 2 + 2 = 13 by decide,
    List.cons_append, List.nil_append] using hall


set_option linter.unusedSimpArgs false in
private theorem run_stage5 (template : State) (pc x0 x1 x2 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stage5
      (framed template pc ([x0,x1,x2,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 5 pc)
      ([accumulator,modulus,modulus,modulus,modulus] ++
        [x0,x1,x2,accumulator,modulus] ++ rest)) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, stage5, framed, Challenge.EvmProof.Stepper.runInstr,
      hrest, h5, h6, h7, h8, h9, h10, h11,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

theorem run_batch5 (template : State) (pc x0 x1 x2 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program5
      (framed template pc ([x0,x1,x2,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 13 pc)
      (WindowMath.squareWordAfter modulus 4 accumulator ::
        [x0,x1,x2,accumulator,modulus] ++ rest)) := by
  let initial := [x0,x1,x2,accumulator,modulus] ++ rest
  let a1 := UInt256.mulMod accumulator accumulator modulus
  let a2 := UInt256.mulMod a1 a1 modulus
  let a3 := UInt256.mulMod a2 a2 modulus
  have h0 := run_stage5 template pc x0 x1 x2 accumulator modulus rest hrest
  have h1 := run_pair template (advancePC 5 pc) accumulator modulus
    ([modulus,modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_pair template (advancePC 2 (advancePC 5 pc)) a1 modulus
    ([modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h3 := run_pair template (advancePC 2 (advancePC 2 (advancePC 5 pc))) a2 modulus
    (modulus :: initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h4 := run_pair template (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 5 pc)))) a3 modulus
    initial (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  have hall := runInstructions_append_some _ _ _ _ _ h0123 h4
  simpa only [program5, initial, a1, a2, a3, WindowMath.squareWordAfter,
    ← advancePC_add, show 5 + 2 + 2 + 2 + 2 = 13 by decide,
    List.cons_append, List.nil_append] using hall


set_option linter.unusedSimpArgs false in
private theorem run_stage4 (template : State) (pc x0 x1 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stage4
      (framed template pc ([x0,x1,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 5 pc)
      ([accumulator,modulus,modulus,modulus,modulus] ++
        [x0,x1,accumulator,modulus] ++ rest)) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, stage4, framed, Challenge.EvmProof.Stepper.runInstr,
      hrest, h4, h5, h6, h7, h8, h9, h10, h11,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

theorem run_batch4 (template : State) (pc x0 x1 accumulator modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program4
      (framed template pc ([x0,x1,accumulator,modulus] ++ rest)) =
    some (framed template (advancePC 13 pc)
      (WindowMath.squareWordAfter modulus 4 accumulator ::
        [x0,x1,accumulator,modulus] ++ rest)) := by
  let initial := [x0,x1,accumulator,modulus] ++ rest
  let a1 := UInt256.mulMod accumulator accumulator modulus
  let a2 := UInt256.mulMod a1 a1 modulus
  let a3 := UInt256.mulMod a2 a2 modulus
  have h0 := run_stage4 template pc x0 x1 accumulator modulus rest hrest
  have h1 := run_pair template (advancePC 5 pc) accumulator modulus
    ([modulus,modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_pair template (advancePC 2 (advancePC 5 pc)) a1 modulus
    ([modulus,modulus] ++ initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h3 := run_pair template (advancePC 2 (advancePC 2 (advancePC 5 pc))) a2 modulus
    (modulus :: initial) (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h4 := run_pair template (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 5 pc)))) a3 modulus
    initial (by simp only [initial, List.length_append, List.length_cons, List.length_nil]; omega)
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  have hall := runInstructions_append_some _ _ _ _ _ h0123 h4
  simpa only [program4, initial, a1, a2, a3, WindowMath.squareWordAfter,
    ← advancePC_add, show 5 + 2 + 2 + 2 + 2 = 13 by decide,
    List.cons_append, List.nil_append] using hall


end Challenge.Modexp.Submission.Proofs.Bytecode.WindowSquareBatch

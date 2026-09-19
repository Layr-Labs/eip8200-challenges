import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLastGroup

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenLast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The last batch starts after four squares and consumes the original modulus. -/
def stageProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩)] ++
    List.replicate 9 (.op (.Dup ⟨0, by decide⟩)) ++
    [.op (.Swap ⟨9, by decide⟩)]

def program (l0 l1 : Nat) : List Instr :=
  stageProgram ++ WindowTwentyOneLookup.program 10 (by decide) l0 ++
    WindowTwentyOneGroup.nibbleProgram 4 (by decide) l1 ++
    (WindowTwentyOneStage.fourSquaresProgram ++ WindowTwentyOneLastGroup.lookupLastProgram)

private theorem run_liftModulus (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Dup ⟨1, by decide⟩)]
      (WindowTwentyOneStage.framed template pc
        ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template pc.succ
      ([modulus, accumulator, modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 5 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneStage.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, Nat.add_assoc]

private theorem run_swap10 (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Swap ⟨9, by decide⟩)]
      (WindowTwentyOneStage.framed template pc
        (List.replicate 10 modulus ++
          [accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template pc.succ
      ((accumulator :: List.replicate 10 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 15 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneStage.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, Nat.add_assoc,
    List.replicate, List.exchange]

theorem run_stage (template : State) (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stageProgram
      (WindowTwentyOneStage.framed template pc
        ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template (advancePC 11 pc)
      ((accumulator :: List.replicate 10 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have h0 := run_liftModulus template pc accumulator modulus exponent mask counter rest hrest
  have h1 := WindowTwentyOneStage.run_topCopies template pc.succ modulus
    ([accumulator, modulus, exponent, mask, counter] ++ rest) 9
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_swap10 template (advancePC 9 pc.succ)
    accumulator modulus exponent mask counter rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  have hpc : (advancePC 9 pc.succ).succ = advancePC 11 pc := rfl
  simpa only [stageProgram, hpc, List.replicate, List.cons_append,
    List.nil_append] using hall

private theorem run_firstLookup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress : WindowTwentyOneGroup.address mem laddr = 32 * index)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (WindowTwentyOneLookup.program 10 (by decide) laddr)
      (WindowTwentyOneGroup.state template pc mem 18 modulus
        (WindowMath.squareWordAfter modulus 4 accumulator) exponent counter 10 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 8 pc) mem 18 modulus
      (WindowMath.nibbleWordStep modulus base accumulator index) exponent counter 9 rest) := by
  let tail := List.replicate 9 modulus ++
    ([modulus, exponent, UInt256.ofNat 480, counter] ++ rest)
  have hmask : tail[11]? = some (UInt256.ofNat 480) := by
    dsimp only [tail]
    rfl
  have h := WindowTwentyOneLookup.run_lookup template pc mem base modulus
    (WindowMath.squareWordAfter modulus 4 accumulator) tail 10 (by decide)
    laddr hladdr index hindex hmask hread haddress
    (by simp only [tail, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]; omega)
  rw [mulMod_comm (WindowMath.tableWord base modulus index)
    (WindowMath.squareWordAfter modulus 4 accumulator) modulus] at h
  simpa only [WindowTwentyOneGroup.state, tail, WindowMath.nibbleWordStep,
    List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append] using h

theorem run_tail (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (l0 l1 : Nat) (hl0 : l0 + 32 ≤ 576) (hl1 : l1 + 32 ≤ 576)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index0 index1 index2 : Nat)
    (hi0 : index0 < 16) (hi1 : index1 < 16) (hi2 : index2 < 16)
    (ha0 : WindowTwentyOneGroup.address mem l0 = 32 * index0)
    (ha1 : WindowTwentyOneGroup.address mem l1 = 32 * index1)
    (ha2 : (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft exponent 4)).toNat = 32 * index2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program l0 l1)
      (WindowTwentyOneGroup.state template pc mem 18 modulus
        (WindowMath.squareWordAfter modulus 4 accumulator) exponent counter 0 rest) =
    some (WindowTwentyOneLastGroup.outState template (advancePC 51 pc) mem 18
      (WindowTwentyOneGroup.accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter rest) := by
  let squared := WindowMath.squareWordAfter modulus 4 accumulator
  let core := WindowTwentyOneLookup.framed template pc mem 18 []
  have hs := run_stage core pc squared modulus exponent (UInt256.ofNat 480) counter rest hrest
  have hs' : runInstructions stageProgram
      (WindowTwentyOneGroup.state template pc mem 18 modulus squared exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 11 pc) mem 18 modulus
      squared exponent counter 10 rest) := by
    simpa only [WindowTwentyOneGroup.state, core, WindowTwentyOneStage.framed,
      WindowTwentyOneLookup.framed, List.replicate_zero, List.nil_append,
      List.cons_append, List.append_assoc] using hs
  have h0 := run_firstLookup template (advancePC 11 pc) mem base modulus accumulator
    exponent counter l0 hl0 index0 hi0 (htable index0 hi0) ha0 rest hrest
  let a1 := WindowMath.nibbleWordStep modulus base accumulator index0
  have h1 := WindowTwentyOneGroup.run_nibble template (advancePC 8 (advancePC 11 pc)) mem
    base modulus a1 exponent counter 4 (by decide) l1 hl1 htable index1 hi1 ha1 rest hrest
  let a2 := WindowMath.nibbleWordStep modulus base a1 index1
  have h2 := WindowTwentyOneLastGroup.run_lastNibble template
    (advancePC 16 (advancePC 8 (advancePC 11 pc))) mem base modulus a2 exponent counter
    htable index2 hi2 ha2 rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ hs' h0
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h1
  have hall := runInstructions_append_some _ _ _ _ _ h012 h2
  simpa only [program, squared, a1, a2, WindowTwentyOneGroup.accumulatorAfter,
    ← advancePC_add, show 11 + 8 + 16 + 16 = 51 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenLast

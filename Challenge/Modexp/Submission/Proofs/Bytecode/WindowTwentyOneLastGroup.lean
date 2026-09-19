import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLastGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def outState (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (accumulator exponent counter : UInt256) (rest : List UInt256) : State :=
  WindowTwentyOneLookup.framed template pc mem active
    ([accumulator, exponent, UInt256.ofNat 480, counter] ++ rest)

def reducedStageProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩)] ++
    List.replicate 13 (.op (.Dup ⟨0, by decide⟩)) ++
    [.op (.Swap ⟨13, by decide⟩)]

def lookupLastProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 4, .op .SHL,
   .op (.Dup ⟨4, by decide⟩), .op .AND,
   .op .MLOAD, .op .MULMOD]

def program (l0 l1 : Nat) : List Instr :=
  reducedStageProgram ++
    WindowTwentyOneGroup.nibbleProgram 9 (by decide) l0 ++
    WindowTwentyOneGroup.nibbleProgram 4 (by decide) l1 ++
    (WindowTwentyOneStage.fourSquaresProgram ++ lookupLastProgram)

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

private theorem run_swap14 (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Swap ⟨13, by decide⟩)]
      (WindowTwentyOneStage.framed template pc
        (List.replicate 14 modulus ++
          [accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template pc.succ
      ((accumulator :: List.replicate 14 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 19 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneStage.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, Nat.add_assoc,
    List.replicate, List.exchange]

private theorem run_reducedStage (template : State) (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions reducedStageProgram
      (WindowTwentyOneStage.framed template pc
        ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template (advancePC 15 pc)
      ((accumulator :: List.replicate 14 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have h0 := run_liftModulus template pc accumulator modulus exponent mask counter rest hrest
  have h1 := WindowTwentyOneStage.run_topCopies template pc.succ modulus
    ([accumulator, modulus, exponent, mask, counter] ++ rest) 13
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_swap14 template (advancePC 13 pc.succ)
    accumulator modulus exponent mask counter rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  have hpc : (advancePC 13 pc.succ).succ = advancePC 15 pc := rfl
  simpa only [reducedStageProgram, hpc, List.replicate, List.cons_append,
    List.nil_append] using hall

private theorem run_lookupLastReduced (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent : UInt256)
    (tail : List UInt256)
    (index : Nat) (hindex : index < 16)
    (hexp : tail[0]? = some exponent)
    (hmask : tail[1]? = some (UInt256.ofNat 480))
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft exponent 4)).toNat = 32 * index)
    (hcap : tail.length + 4 < 1024) :
    runInstructions lookupLastProgram
      (WindowTwentyOneLookup.framed template pc mem 18 (accumulator :: modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 8 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hpush2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, lookupLastProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, hcap3,
      List.getElem?_cons_succ, h18,
      hexp, hmask, haddress, hread, hactive, State.activeWordsAfterUInt256,
      advancePC, succ_eq_add, hpush2, word_add_assoc]

theorem run_lastNibble (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index : Nat) (hindex : index < 16)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (UInt256.shiftLeft exponent 4)).toNat = 32 * index)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (WindowTwentyOneStage.fourSquaresProgram ++ lookupLastProgram)
      (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 4 rest) =
    some (outState template (advancePC 16 pc) mem 18
      (WindowMath.nibbleWordStep modulus base accumulator index) exponent counter rest) := by
  let tail := [exponent, UInt256.ofNat 480, counter] ++ rest
  let core := WindowTwentyOneLookup.framed template pc mem 18 []
  let squared := WindowMath.squareWordAfter modulus 4 accumulator
  have hsquare := WindowTwentyOneStage.run_fourSquares core pc accumulator modulus
    (modulus :: tail)
    (by simp only [tail, List.length_append, List.length_cons, List.length_nil]; omega)
  have hsquare' :
      runInstructions WindowTwentyOneStage.fourSquaresProgram
        (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 4 rest) =
      some (WindowTwentyOneLookup.framed template (advancePC 8 pc) mem 18
        (squared :: modulus :: tail)) := by
    simpa only [WindowTwentyOneGroup.state, core, tail, squared,
      WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed,
      List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append] using hsquare
  have hexp : tail[0]? = some exponent := by
    dsimp only [tail]
    rfl
  have hmask : tail[1]? = some (UInt256.ofNat 480) := by
    dsimp only [tail]
    rfl
  have hlookup := run_lookupLastReduced template (advancePC 8 pc) mem
    base modulus squared exponent tail index hindex hexp hmask
    (htable index hindex) haddress
    (by simp only [tail, List.length_append, List.length_cons, List.length_nil]; omega)
  rw [mulMod_comm (WindowMath.tableWord base modulus index) squared modulus] at hlookup
  have both := runInstructions_append_some _ _ _ _ _ hsquare' hlookup
  simpa only [outState, tail, squared, WindowMath.nibbleWordStep,
    ← advancePC_add, show 8 + 8 = 16 by decide, List.cons_append,
    List.nil_append] using both

theorem run_group (template : State) (pc : UInt256) (mem : ByteArray)
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
      (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
    some (outState template (advancePC 63 pc) mem 18
      (WindowTwentyOneGroup.accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter rest) := by
  let core := WindowTwentyOneLookup.framed template pc mem 18 []
  have hs := run_reducedStage core pc accumulator modulus exponent
    (UInt256.ofNat 480) counter rest hrest
  have hs' :
      runInstructions reducedStageProgram
        (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 15 pc) mem 18 modulus
        accumulator exponent counter 14 rest) := by
    simpa only [WindowTwentyOneGroup.state, core, WindowTwentyOneStage.framed,
      WindowTwentyOneLookup.framed, List.replicate_zero, List.nil_append,
      List.cons_append, List.append_assoc] using hs
  let a1 := WindowMath.nibbleWordStep modulus base accumulator index0
  have h0 := WindowTwentyOneGroup.run_nibble template (advancePC 15 pc) mem
    base modulus accumulator exponent counter 9 (by decide) l0 hl0 htable index0 hi0 ha0
    rest hrest
  let a2 := WindowMath.nibbleWordStep modulus base a1 index1
  have h1 := WindowTwentyOneGroup.run_nibble template
    (advancePC 16 (advancePC 15 pc)) mem base modulus a1 exponent counter
    4 (by decide) l1 hl1 htable index1 hi1 ha1 rest hrest
  have h2 := run_lastNibble template
    (advancePC 16 (advancePC 16 (advancePC 15 pc))) mem
    base modulus a2 exponent counter htable index2 hi2 ha2 rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ hs' h0
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h1
  have hall := runInstructions_append_some _ _ _ _ _ h012 h2
  simpa only [program, a1, a2, WindowTwentyOneGroup.accumulatorAfter,
    ← advancePC_add, show 15 + 16 + 16 + 16 = 63 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLastGroup

import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineStage
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLookup

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def state (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (copies : Nat) (rest : List UInt256) : State :=
  WindowNineLookup.framed template pc base modulus
    (accumulator :: List.replicate copies modulus ++
      ([modulus, exponent, UInt256.ofNat 480, counter] ++ rest))

def address (exponent : UInt256) (shift : Fin 256) : Nat :=
  (UInt256.land (UInt256.ofNat 480)
    (UInt256.shiftRight exponent (UInt256.ofNat shift.val))).toNat

def nibbleProgram (copies : Nat) (hcopies : copies ≤ 10) (shift : Fin 256) : List Instr :=
  WindowNineStage.fourSquaresProgram ++
    WindowNineLookup.program (copies + 1) (by omega) shift

/-- One staged nibble consumes five modulus copies and leaves its entire tail. -/
theorem run_nibble (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (copies : Nat) (hcopies : copies ≤ 10) (shift : Fin 256)
    (index : Nat) (hindex : index < 16) (haddress : address exponent shift = 32 * index)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (nibbleProgram copies hcopies shift)
      (state template pc base modulus accumulator exponent counter (copies + 5) rest) =
    some (state template (advancePC 16 pc) base modulus
      (WindowMath.nibbleWordStep modulus base accumulator index)
      exponent counter copies rest) := by
  let tail := List.replicate copies modulus ++
    ([modulus, exponent, UInt256.ofNat 480, counter] ++ rest)
  let core := WindowNineLookup.framed template pc base modulus []
  let squared := WindowMath.squareWordAfter modulus 4 accumulator
  have hsquare := WindowNineStage.run_fourSquares core pc accumulator modulus
    (modulus :: tail)
    (by simp only [tail, List.length_cons, List.length_append, List.length_replicate,
          List.length_nil]; omega)
  have hsquare' :
      runInstructions WindowNineStage.fourSquaresProgram
        (state template pc base modulus accumulator exponent counter (copies + 5) rest) =
      some (WindowNineLookup.framed template (advancePC 8 pc) base modulus
        (squared :: modulus :: tail)) := by
    simpa only [state, core, tail, squared, WindowNineStage.framed,
      WindowNineLookup.framed, List.replicate_succ, List.cons_append, List.nil_append] using hsquare
  have hexponent : tail[copies + 1]? = some exponent := by
    dsimp only [tail]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hmask : tail[copies + 2]? = some (UInt256.ofNat 480) := by
    dsimp only [tail]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hlookup := WindowNineLookup.run_lookup template (advancePC 8 pc)
    base modulus squared exponent tail (copies + 1) (by omega) shift index hindex
    hexponent hmask haddress
    (by simp only [tail, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]; omega)
  rw [mulMod_comm (WindowMath.tableWord base modulus index) squared modulus] at hlookup
  have both := runInstructions_append_some _ _ _ _ _ hsquare' hlookup
  simpa only [nibbleProgram, state, tail, squared, WindowMath.nibbleWordStep,
    ← advancePC_add, show 8 + 8 = 16 by decide, List.cons_append] using both

def program (shift0 shift1 shift2 : Fin 256) : List Instr :=
  WindowNineStage.stageProgram ++ nibbleProgram 10 (by decide) shift0 ++
    nibbleProgram 5 (by decide) shift1 ++ nibbleProgram 0 (by decide) shift2

def accumulatorAfter (base modulus accumulator : UInt256)
    (index0 index1 index2 : Nat) : UInt256 :=
  WindowMath.nibbleWordStep modulus base
    (WindowMath.nibbleWordStep modulus base
      (WindowMath.nibbleWordStep modulus base accumulator index0) index1) index2

/-- One physical 64-byte group processes three nibbles and restores the five-slot frame. -/
theorem run_group (template : State) (pc base modulus accumulator exponent counter : UInt256)
    (shift0 shift1 shift2 : Fin 256) (index0 index1 index2 : Nat)
    (hi0 : index0 < 16) (hi1 : index1 < 16) (hi2 : index2 < 16)
    (ha0 : address exponent shift0 = 32 * index0)
    (ha1 : address exponent shift1 = 32 * index1)
    (ha2 : address exponent shift2 = 32 * index2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program shift0 shift1 shift2)
      (state template pc base modulus accumulator exponent counter 0 rest) =
    some (state template (advancePC 64 pc) base modulus
      (accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter 0 rest) := by
  let core := WindowNineLookup.framed template pc base modulus []
  let a1 := WindowMath.nibbleWordStep modulus base accumulator index0
  let a2 := WindowMath.nibbleWordStep modulus base a1 index1
  have hs := WindowNineStage.run_stage core pc accumulator modulus exponent
    (UInt256.ofNat 480) counter rest hrest
  have hs' :
      runInstructions WindowNineStage.stageProgram
        (state template pc base modulus accumulator exponent counter 0 rest) =
      some (state template (advancePC 16 pc) base modulus accumulator exponent counter 15 rest) := by
    simpa only [state, core, WindowNineStage.framed, WindowNineLookup.framed,
      List.replicate_zero, List.nil_append, List.cons_append, List.append_assoc] using hs
  have h0 := run_nibble template (advancePC 16 pc) base modulus accumulator exponent counter
    10 (by decide) shift0 index0 hi0 ha0 rest hrest
  have h1 := run_nibble template (advancePC 16 (advancePC 16 pc)) base modulus a1 exponent counter
    5 (by decide) shift1 index1 hi1 ha1 rest hrest
  have h2 := run_nibble template (advancePC 16 (advancePC 16 (advancePC 16 pc)))
    base modulus a2 exponent counter 0 (by decide) shift2 index2 hi2 ha2 rest hrest
  have hs0 := runInstructions_append_some _ _ _ _ _ hs' h0
  have hs01 := runInstructions_append_some _ _ _ _ _ hs0 h1
  have hall := runInstructions_append_some _ _ _ _ _ hs01 h2
  simpa only [program, a1, a2, accumulatorAfter, ← advancePC_add,
    show 16 + 16 + 16 + 16 = 64 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGroup

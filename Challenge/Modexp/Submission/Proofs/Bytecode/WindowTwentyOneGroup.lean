import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLookup

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def state (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (modulus accumulator exponent counter : UInt256)
    (copies : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneLookup.framed template pc mem active
    (accumulator :: List.replicate copies modulus ++
      ([modulus, exponent, UInt256.ofNat 480, counter] ++ rest))

/-- After the trampoline's five staging instructions (`stageHead`). -/
def headState (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (modulus accumulator exponent counter : UInt256) (rest : List UInt256) : State :=
  WindowTwentyOneLookup.framed template pc mem active
    (List.replicate 5 modulus ++ ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest))

/-- The table index a lookup at `laddr` selects. -/
def address (mem : ByteArray) (laddr : Nat) : Nat :=
  (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat

def nibbleProgram (copies : Nat) (hcopies : copies ≤ 10) (laddr : Nat) : List Instr :=
  WindowTwentyOneStage.fourSquaresProgram ++
    WindowTwentyOneLookup.program (copies + 1) (by omega) laddr

/-- One staged nibble consumes five modulus copies and leaves its entire tail. -/
theorem run_nibble (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (copies : Nat) (hcopies : copies ≤ 10) (laddr : Nat) (hladdr : laddr + 32 ≤ 608)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index : Nat) (hindex : index < 16) (haddress : address mem laddr = 32 * index)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (nibbleProgram copies hcopies laddr)
      (state template pc mem 19 modulus accumulator exponent counter (copies + 5) rest) =
    some (state template (advancePC 16 pc) mem 19 modulus
      (WindowMath.nibbleWordStep modulus base accumulator index)
      exponent counter copies rest) := by
  let tail := List.replicate copies modulus ++
    ([modulus, exponent, UInt256.ofNat 480, counter] ++ rest)
  let core := WindowTwentyOneLookup.framed template pc mem 19 []
  let squared := WindowMath.squareWordAfter modulus 4 accumulator
  have hsquare := WindowTwentyOneStage.run_fourSquares core pc accumulator modulus
    (modulus :: tail)
    (by simp only [tail, List.length_cons, List.length_append, List.length_replicate,
          List.length_nil]; omega)
  have hsquare' :
      runInstructions WindowTwentyOneStage.fourSquaresProgram
        (state template pc mem 19 modulus accumulator exponent counter (copies + 5) rest) =
      some (WindowTwentyOneLookup.framed template (advancePC 8 pc) mem 19
        (squared :: modulus :: tail)) := by
    simpa only [state, core, tail, squared, WindowTwentyOneStage.framed,
      WindowTwentyOneLookup.framed, List.replicate_succ, List.cons_append, List.nil_append] using hsquare
  have hmask : tail[copies + 2]? = some (UInt256.ofNat 480) := by
    dsimp only [tail]
    rw [List.getElem?_append_right (by simp)]
    simp
  have hlookup := WindowTwentyOneLookup.run_lookup template (advancePC 8 pc) mem
    base modulus squared tail (copies + 1) (by omega) laddr hladdr index hindex
    hmask (htable index hindex) haddress
    (by simp only [tail, List.length_append, List.length_replicate,
          List.length_cons, List.length_nil]; omega)
  rw [mulMod_comm (WindowMath.tableWord base modulus index) squared modulus] at hlookup
  have both := runInstructions_append_some _ _ _ _ _ hsquare' hlookup
  simpa only [nibbleProgram, state, tail, squared, WindowMath.nibbleWordStep,
    ← advancePC_add, show 8 + 8 = 16 by decide, List.cons_append] using both

def nibblesProgram (l0 l1 l2 : Nat) : List Instr :=
  nibbleProgram 10 (by decide) l0 ++ nibbleProgram 5 (by decide) l1 ++ nibbleProgram 0 (by decide) l2

def program (l0 l1 l2 : Nat) : List Instr :=
  WindowTwentyOneStage.stageProgram ++ nibblesProgram l0 l1 l2

/-- The first group of each pass: its first five staging instructions run in the trampoline. -/
def restProgram (l0 l1 l2 : Nat) : List Instr :=
  WindowTwentyOneStage.stageRest ++ nibblesProgram l0 l1 l2

def accumulatorAfter (base modulus accumulator : UInt256)
    (index0 index1 index2 : Nat) : UInt256 :=
  WindowMath.nibbleWordStep modulus base
    (WindowMath.nibbleWordStep modulus base
      (WindowMath.nibbleWordStep modulus base accumulator index0) index1) index2

theorem run_nibbles (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (l0 l1 l2 : Nat) (hl0 : l0 + 32 ≤ 608) (hl1 : l1 + 32 ≤ 608) (hl2 : l2 + 32 ≤ 608)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index0 index1 index2 : Nat)
    (hi0 : index0 < 16) (hi1 : index1 < 16) (hi2 : index2 < 16)
    (ha0 : address mem l0 = 32 * index0)
    (ha1 : address mem l1 = 32 * index1)
    (ha2 : address mem l2 = 32 * index2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (nibblesProgram l0 l1 l2)
      (state template pc mem 19 modulus accumulator exponent counter 15 rest) =
    some (state template (advancePC 48 pc) mem 19 modulus
      (accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter 0 rest) := by
  let a1 := WindowMath.nibbleWordStep modulus base accumulator index0
  let a2 := WindowMath.nibbleWordStep modulus base a1 index1
  have h0 := run_nibble template pc mem base modulus accumulator exponent counter
    10 (by decide) l0 hl0 htable index0 hi0 ha0 rest hrest
  have h1 := run_nibble template (advancePC 16 pc) mem base modulus a1 exponent counter
    5 (by decide) l1 hl1 htable index1 hi1 ha1 rest hrest
  have h2 := run_nibble template (advancePC 16 (advancePC 16 pc)) mem
    base modulus a2 exponent counter 0 (by decide) l2 hl2 htable index2 hi2 ha2 rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  simpa only [nibblesProgram, a1, a2, accumulatorAfter, ← advancePC_add,
    show 16 + 16 + 16 = 48 by decide] using hall

/-- One physical 64-byte group processes three nibbles and restores the five-slot frame. -/
theorem run_group (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (l0 l1 l2 : Nat) (hl0 : l0 + 32 ≤ 608) (hl1 : l1 + 32 ≤ 608) (hl2 : l2 + 32 ≤ 608)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index0 index1 index2 : Nat)
    (hi0 : index0 < 16) (hi1 : index1 < 16) (hi2 : index2 < 16)
    (ha0 : address mem l0 = 32 * index0)
    (ha1 : address mem l1 = 32 * index1)
    (ha2 : address mem l2 = 32 * index2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program l0 l1 l2)
      (state template pc mem 19 modulus accumulator exponent counter 0 rest) =
    some (state template (advancePC 64 pc) mem 19 modulus
      (accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter 0 rest) := by
  let core := WindowTwentyOneLookup.framed template pc mem 19 []
  have hs := WindowTwentyOneStage.run_stage core pc accumulator modulus exponent
    (UInt256.ofNat 480) counter rest hrest
  have hs' :
      runInstructions WindowTwentyOneStage.stageProgram
        (state template pc mem 19 modulus accumulator exponent counter 0 rest) =
      some (state template (advancePC 16 pc) mem 19 modulus accumulator exponent counter 15 rest) := by
    simpa only [state, core, WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed,
      List.replicate_zero, List.nil_append, List.cons_append, List.append_assoc] using hs
  have hn := run_nibbles template (advancePC 16 pc) mem base modulus accumulator exponent counter
    l0 l1 l2 hl0 hl1 hl2 htable index0 index1 index2 hi0 hi1 hi2 ha0 ha1 ha2 rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hs' hn
  simpa only [program, ← advancePC_add, show 16 + 48 = 64 by decide] using hall

/-- The pass's first group, resumed after the trampoline's `stageHead`. -/
theorem run_restGroup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (l0 l1 l2 : Nat) (hl0 : l0 + 32 ≤ 608) (hl1 : l1 + 32 ≤ 608) (hl2 : l2 + 32 ≤ 608)
    (htable : ∀ i, i < 16 → MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (index0 index1 index2 : Nat)
    (hi0 : index0 < 16) (hi1 : index1 < 16) (hi2 : index2 < 16)
    (ha0 : address mem l0 = 32 * index0)
    (ha1 : address mem l1 = 32 * index1)
    (ha2 : address mem l2 = 32 * index2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (restProgram l0 l1 l2)
      (headState template pc mem 19 modulus accumulator exponent counter rest) =
    some (state template (advancePC 59 pc) mem 19 modulus
      (accumulatorAfter base modulus accumulator index0 index1 index2)
      exponent counter 0 rest) := by
  let core := WindowTwentyOneLookup.framed template pc mem 19 []
  have hs := WindowTwentyOneStage.run_stageRest core pc accumulator modulus exponent
    (UInt256.ofNat 480) counter rest hrest
  have hs' :
      runInstructions WindowTwentyOneStage.stageRest
        (headState template pc mem 19 modulus accumulator exponent counter rest) =
      some (state template (advancePC 11 pc) mem 19 modulus accumulator exponent counter 15 rest) := by
    simpa only [headState, state, core, WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed,
      List.replicate_zero, List.nil_append, List.cons_append, List.append_assoc] using hs
  have hn := run_nibbles template (advancePC 11 pc) mem base modulus accumulator exponent counter
    l0 l1 l2 hl0 hl1 hl2 htable index0 index1 index2 hi0 hi1 hi2 ha0 ha1 ha2 rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hs' hn
  simpa only [restProgram, ← advancePC_add, show 11 + 48 = 59 by decide] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup

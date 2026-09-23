import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

/-!
Sixteen-operation modulus batches proposed by GPT 6 Pro.
Pure execution lemmas cover the four-batch prefix and full sixteen-digit block.
Concrete bytecode bindings and the final fifteen-digit block are separate.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBlock

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode

namespace Stage

def stage16Program : List Instr :=
  [.op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨15, by decide⟩)]

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

private theorem run_swap16 (template : State)
    (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op (.Swap ⟨15, by decide⟩)]
      (WindowTwentyOneStage.framed template pc
        (List.replicate 16 modulus ++
          ([accumulator, modulus, exponent, mask, counter] ++ rest))) =
    some (WindowTwentyOneStage.framed template pc.succ
      ((accumulator :: List.replicate 16 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have hcap : rest.length + 21 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneStage.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, Nat.add_assoc,
    List.replicate, List.exchange]

theorem run_stage16 (template : State) (pc accumulator modulus exponent mask counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions stage16Program
      (WindowTwentyOneStage.framed template pc
        ([accumulator, modulus, exponent, mask, counter] ++ rest)) =
    some (WindowTwentyOneStage.framed template (advancePC 17 pc)
      ((accumulator :: List.replicate 16 modulus) ++
        [modulus, exponent, mask, counter] ++ rest)) := by
  have h0 := run_liftModulus template pc accumulator modulus exponent mask counter rest hrest
  have h1 := WindowTwentyOneStage.run_topCopies template pc.succ modulus
    ([accumulator, modulus, exponent, mask, counter] ++ rest) 15
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have h2 := run_swap16 template (advancePC 15 pc.succ)
    accumulator modulus exponent mask counter rest hrest
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have hall := runInstructions_append_some _ _ _ _ _ h01 h2
  have hpc : (advancePC 15 pc.succ).succ = advancePC 17 pc := rfl
  simpa only [stage16Program, hpc, List.replicate, List.cons_append, List.nil_append] using hall

end Stage

namespace Lookup

def lookupImmediateProgram (laddr : Nat) : List Instr :=
  [.push 2 (UInt256.ofNat laddr), .op .MLOAD,
   .push 2 (UInt256.ofNat 480), .op .AND,
   .op .MLOAD, .op .MULMOD]

theorem run_lookupImmediate (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator : UInt256)
    (tail : List UInt256) (laddr : Nat)
    (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) = WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat = 32 * index)
    (hcap : tail.length + 4 < 1024) :
    runInstructions (lookupImmediateProgram laddr)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 10 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hl : (UInt256.ofNat laddr).toNat = laddr := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h18 : (UInt256.ofNat 18).toNat = 18 := rfl
  have hactive := WindowTwentyOneLookup.activeWordsAfter_table index hindex
  have hactive' := WindowCopyMemory.activeWordsAfter_eighteen laddr hladdr
  have hpush3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp (disch := omega)
    [runInstructions, lookupImmediateProgram, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, hcap3,
      hl, h18, haddress, hread, hactive, hactive',
      State.activeWordsAfterUInt256, advancePC, succ_eq_add, hpush3, word_add_assoc]

end Lookup

namespace Block

def squareProgram : List Instr :=
  WindowTwentyOneStage.pairProgram

def squares : Nat → List Instr
  | 0 => []
  | count + 1 => squareProgram ++ squares count

private theorem run_square (template : State) (pc : UInt256) (mem : ByteArray)
    (active : Nat) (modulus accumulator : UInt256) (tail : List UInt256)
    (hcap : tail.length + 3 < 1024) :
    runInstructions squareProgram
      (WindowTwentyOneLookup.framed template pc mem active
        (accumulator :: modulus :: tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC 2 pc) mem active
      (UInt256.mulMod accumulator accumulator modulus :: tail)) := by
  have hcap2 : tail.length + 2 < 1024 := by omega
  simp (disch := omega)
    [runInstructions, squareProgram, WindowTwentyOneStage.pairProgram,
      WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap, hcap2,
      List.getElem?_cons_zero, advancePC]

private theorem squareWordAfter_succ (modulus accumulator : UInt256) (count : Nat) :
    WindowMath.squareWordAfter modulus count
        (UInt256.mulMod accumulator accumulator modulus) =
      WindowMath.squareWordAfter modulus (count + 1) accumulator := by
  induction count with
  | zero => simp [WindowMath.squareWordAfter]
  | succ count ih =>
      simpa only [WindowMath.squareWordAfter] using
        congrArg (fun value => UInt256.mulMod value value modulus) ih

theorem run_squares (template : State) (pc : UInt256) (mem : ByteArray)
    (active : Nat) (modulus accumulator : UInt256) (tail : List UInt256)
    (count : Nat) (hcount : count ≤ 4)
    (hcap : tail.length + count + 2 < 1024) :
    runInstructions (squares count)
      (WindowTwentyOneLookup.framed template pc mem active
        (accumulator :: List.replicate count modulus ++ tail)) =
    some (WindowTwentyOneLookup.framed template (advancePC (2 * count) pc)
      mem active (WindowMath.squareWordAfter modulus count accumulator :: tail)) := by
  induction count generalizing pc accumulator with
  | zero =>
      simp only [squares, runInstructions, WindowMath.squareWordAfter,
        List.replicate_zero, List.nil_append, List.cons_append, advancePC]
  | succ count ih =>
      have hs := run_square template pc mem active modulus accumulator
        (List.replicate count modulus ++ tail) (by
          simp only [List.length_append, List.length_replicate]
          omega)
      have hi := ih (pc := advancePC 2 pc)
        (accumulator := UInt256.mulMod accumulator accumulator modulus)
        (by omega) (by omega)
      have hall := runInstructions_append_some _ _ _ _ _ hs hi
      have hpc : advancePC (2 * count) (advancePC 2 pc) =
          advancePC (2 * (count + 1)) pc := by
        rw [← advancePC_add]
        congr 1
        omega
      simpa only [squares, List.replicate_succ, List.cons_append,
        List.nil_append, hpc, squareWordAfter_succ, Nat.mul_succ] using hall

def lookupDup (slot laddr : Nat) (hslot : slot ≤ 11) : List Instr :=
  WindowTwentyOneLookup.program slot hslot laddr

theorem run_lookupDup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining slot : Nat)
    (hremaining : 1 ≤ remaining) (hslot : slot + 1 = remaining)
    (hslot' : slot ≤ 11) (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (lookupDup slot laddr hslot')
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template (advancePC 8 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: List.replicate (remaining - 1) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  let tail := List.replicate (remaining - 1) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hmask : tail[slot + 1]? = some (UInt256.ofNat 480) := by
    dsimp only [tail]
    rw [hslot]
    rw [List.getElem?_append_right (by
      simp only [List.length_replicate]
      omega)]
    have hrem : remaining - (remaining - 1) = 1 := by omega
    simp [hrem]
  have hcap : tail.length + 4 < 1024 := by
    simp only [tail, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hrun := WindowTwentyOneLookup.run_lookup template pc mem base modulus
    accumulator tail slot hslot' laddr hladdr index hindex hmask hread haddress hcap
  have hrep : List.replicate remaining modulus =
      modulus :: List.replicate (remaining - 1) modulus := by
    calc
      List.replicate remaining modulus =
          List.replicate ((remaining - 1) + 1) modulus := by
            congr 1
            omega
      _ = modulus :: List.replicate (remaining - 1) modulus := by
        rw [List.replicate_succ]
  simpa only [lookupDup, tail, hrep, List.cons_append] using hrun

theorem run_lookupImmediateAt (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining : Nat) (hremaining : 1 ≤ remaining)
    (hremaining' : remaining ≤ 17)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (Lookup.lookupImmediateProgram laddr)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template (advancePC 10 pc) mem 18
      (UInt256.mulMod (WindowMath.tableWord base modulus index)
        accumulator modulus :: List.replicate (remaining - 1) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  let tail := List.replicate (remaining - 1) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hcap : tail.length + 4 < 1024 := by
    simp only [tail, List.length_append, List.length_replicate,
      List.length_cons, List.length_nil]
    omega
  have hrun := Lookup.run_lookupImmediate template pc mem base modulus accumulator
    tail laddr hladdr index hindex hread haddress hcap
  have hrep : List.replicate remaining modulus =
      modulus :: List.replicate (remaining - 1) modulus := by
    calc
      List.replicate remaining modulus =
          List.replicate ((remaining - 1) + 1) modulus := by
            congr 1
            omega
      _ = modulus :: List.replicate (remaining - 1) modulus := by
        rw [List.replicate_succ]
  simpa only [tail, hrep, List.cons_append] using hrun

theorem replicate_split (modulus : UInt256) (remaining left : Nat)
    (hleft : left ≤ remaining) :
    List.replicate remaining modulus =
      List.replicate left modulus ++ List.replicate (remaining - left) modulus := by
  rw [← List.replicate_add]
  congr 1
  omega

theorem run_stageAt (template : State) (pc : UInt256) (mem : ByteArray)
    (modulus accumulator exponent counter : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions Stage.stage16Program
      (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 17 pc) mem 18 modulus
      accumulator exponent counter 16 rest) := by
  let core := WindowTwentyOneLookup.framed template pc mem 18 []
  have hs := Stage.run_stage16 core pc accumulator modulus exponent
    (UInt256.ofNat 480) counter rest hrest
  simpa only [WindowTwentyOneGroup.state, core, WindowTwentyOneStage.framed,
    WindowTwentyOneLookup.framed, List.replicate_zero, List.nil_append,
    List.cons_append, List.append_assoc] using hs

theorem run_phaseImmediate (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining count : Nat)
    (hcount : count ≤ 4) (hremaining : count + 1 ≤ remaining)
    (hremaining' : remaining ≤ 17)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (squares count ++ Lookup.lookupImmediateProgram laddr)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template
      (advancePC (2 * count + 10) pc) mem 18
      (UInt256.mulMod (WindowMath.squareWordAfter modulus count accumulator)
          (WindowMath.tableWord base modulus index) modulus ::
        List.replicate (remaining - count - 1) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  have hsplit := replicate_split modulus remaining count (by omega)
  let tail := List.replicate (remaining - count) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hs := run_squares template pc mem 18 modulus accumulator tail count
    hcount (by
      simp only [tail, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega)
  have hl := run_lookupImmediateAt template (advancePC (2 * count) pc) mem
    base modulus (WindowMath.squareWordAfter modulus count accumulator) exponent counter
    rest (remaining - count) (by omega) (by omega) laddr hladdr index hindex hread
    haddress hrest
  rw [mulMod_comm (WindowMath.tableWord base modulus index)
      (WindowMath.squareWordAfter modulus count accumulator) modulus] at hl
  have hall := runInstructions_append_some _ _ _ _ _ hs hl
  have hpc : advancePC 10 (advancePC (2 * count) pc) =
      advancePC (2 * count + 10) pc := by
    rw [← advancePC_add]
  simpa only [tail, hsplit, squares, hpc, List.replicate_zero,
    List.replicate_succ, List.cons_append, List.nil_append,
    List.append_assoc] using hall

theorem run_phaseDup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining count slot : Nat)
    (hcount : count ≤ 4) (hremaining : count + 1 ≤ remaining)
    (hslot : slot + 1 = remaining - count)
    (hslot' : slot ≤ 11)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (squares count ++ lookupDup slot laddr hslot')
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template
      (advancePC (2 * count + 8) pc) mem 18
      (UInt256.mulMod (WindowMath.squareWordAfter modulus count accumulator)
          (WindowMath.tableWord base modulus index) modulus ::
        List.replicate (remaining - count - 1) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  have hsplit := replicate_split modulus remaining count (by omega)
  let tail := List.replicate (remaining - count) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hs := run_squares template pc mem 18 modulus accumulator tail count
    hcount (by
      simp only [tail, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega)
  have hl := run_lookupDup template (advancePC (2 * count) pc) mem base modulus
    (WindowMath.squareWordAfter modulus count accumulator) exponent counter rest
    (remaining - count) slot (by omega) hslot hslot' laddr hladdr index hindex hread
    haddress hrest
  rw [mulMod_comm (WindowMath.tableWord base modulus index)
      (WindowMath.squareWordAfter modulus count accumulator) modulus] at hl
  have hall := runInstructions_append_some _ _ _ _ _ hs hl
  have hpc : advancePC 8 (advancePC (2 * count) pc) =
      advancePC (2 * count + 8) pc := by
    rw [← advancePC_add]
  simpa only [tail, hsplit, squares, lookupDup, hpc, List.replicate_zero,
    List.replicate_succ, List.cons_append, List.nil_append,
    List.append_assoc] using hall

private theorem run_digitImmediate (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining : Nat)
    (hremaining : 5 ≤ remaining) (hremaining' : remaining ≤ 17)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (squares 4 ++ Lookup.lookupImmediateProgram laddr)
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template (advancePC 18 pc) mem 18
      (WindowMath.nibbleWordStep modulus base accumulator index ::
        List.replicate (remaining - 5) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  have hsplit := replicate_split modulus remaining 4 (by omega)
  let tail := List.replicate (remaining - 4) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hs := run_squares template pc mem 18 modulus accumulator tail 4
    (by decide) (by
      simp only [tail, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega)
  have hl := run_lookupImmediateAt template (advancePC 8 pc) mem base modulus
    (WindowMath.squareWordAfter modulus 4 accumulator) exponent counter rest
    (remaining - 4) (by omega) (by omega) laddr hladdr index hindex hread haddress hrest
  rw [mulMod_comm (WindowMath.tableWord base modulus index)
      (WindowMath.squareWordAfter modulus 4 accumulator) modulus] at hl
  have hall := runInstructions_append_some _ _ _ _ _ hs hl
  have hpc : advancePC 10 (advancePC 8 pc) = advancePC 18 pc := by
    rw [← advancePC_add]
  have hsub : remaining - 4 - 1 = remaining - 5 := by omega
  simpa only [tail, hsplit, squares, hpc, hsub, WindowMath.nibbleWordStep,
    List.replicate_zero, List.replicate_succ, List.cons_append,
    List.nil_append] using hall

private theorem run_digitDup (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (remaining slot : Nat)
    (hremaining : 5 ≤ remaining) (hremaining' : remaining ≤ 16)
    (hslot : slot + 1 = remaining - 4) (hslot' : slot ≤ 11)
    (laddr : Nat) (hladdr : laddr + 32 ≤ 576)
    (index : Nat) (hindex : index < 16)
    (hread : MachineState.readWord mem (32 * index) =
      WindowMath.tableWord base modulus index)
    (haddress :
      (UInt256.land (UInt256.ofNat 480) (MachineState.readWord mem laddr)).toNat =
        32 * index)
    (hrest : rest.length ≤ 1000) :
    runInstructions (squares 4 ++ lookupDup slot laddr hslot')
      (WindowTwentyOneLookup.framed template pc mem 18
        (accumulator :: List.replicate remaining modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) =
    some (WindowTwentyOneLookup.framed template (advancePC 16 pc) mem 18
      (WindowMath.nibbleWordStep modulus base accumulator index ::
        List.replicate (remaining - 5) modulus ++
          ([exponent, UInt256.ofNat 480, counter] ++ rest))) := by
  have hsplit := replicate_split modulus remaining 4 (by omega)
  let tail := List.replicate (remaining - 4) modulus ++
    ([exponent, UInt256.ofNat 480, counter] ++ rest)
  have hs := run_squares template pc mem 18 modulus accumulator tail 4
    (by decide) (by
      simp only [tail, List.length_append, List.length_replicate,
        List.length_cons, List.length_nil]
      omega)
  have hl := run_lookupDup template (advancePC 8 pc) mem base modulus
    (WindowMath.squareWordAfter modulus 4 accumulator) exponent counter rest
    (remaining - 4) slot (by omega) hslot hslot' laddr hladdr index hindex hread
    haddress hrest
  rw [mulMod_comm (WindowMath.tableWord base modulus index)
      (WindowMath.squareWordAfter modulus 4 accumulator) modulus] at hl
  have hall := runInstructions_append_some _ _ _ _ _ hs hl
  have hpc : advancePC 8 (advancePC 8 pc) = advancePC 16 pc := by
    rw [← advancePC_add]
  have hsub : remaining - 4 - 1 = remaining - 5 := by omega
  simpa only [tail, hsplit, squares, lookupDup, hpc, hsub,
    WindowMath.nibbleWordStep, List.replicate_zero, List.replicate_succ,
    List.cons_append, List.nil_append] using hall

def immediateAt (index : Nat) : List Instr :=
  Lookup.lookupImmediateProgram (WindowCopyMemory.laddr index)

def dupAt (slot index : Nat) (hslot : slot ≤ 11) : List Instr :=
  lookupDup slot (WindowCopyMemory.laddr index) hslot

def batch0 (off : Nat) : List Instr :=
  Stage.stage16Program ++
    squares 4 ++ immediateAt (off + 0) ++
    squares 4 ++ dupAt 7 (off + 1) (by decide) ++
    squares 4 ++ dupAt 2 (off + 2) (by decide) ++
    squares 1

def batch1 (off : Nat) : List Instr :=
  Stage.stage16Program ++
    squares 3 ++ immediateAt (off + 3) ++
    squares 4 ++ dupAt 8 (off + 4) (by decide) ++
    squares 4 ++ dupAt 3 (off + 5) (by decide) ++
    squares 2

def batch2 (off : Nat) : List Instr :=
  Stage.stage16Program ++
    squares 2 ++ immediateAt (off + 6) ++
    squares 4 ++ dupAt 9 (off + 7) (by decide) ++
    squares 4 ++ dupAt 4 (off + 8) (by decide) ++
    squares 3

def batch3 (off : Nat) : List Instr :=
  Stage.stage16Program ++
    squares 1 ++ immediateAt (off + 9) ++
    squares 4 ++ dupAt 10 (off + 10) (by decide) ++
    squares 4 ++ dupAt 5 (off + 11) (by decide) ++
    squares 4

def batch4 (off : Nat) : List Instr :=
  Stage.stage16Program ++
    immediateAt (off + 12) ++
    squares 4 ++ dupAt 11 (off + 13) (by decide) ++
    squares 4 ++ dupAt 6 (off + 14) (by decide) ++
    squares 4 ++ dupAt 1 (off + 15) (by decide)

def program80Prefix (off : Nat) : List Instr :=
  batch0 off ++ batch1 off ++ batch2 off ++ batch3 off

def program80 (off : Nat) : List Instr :=
  program80Prefix off ++ batch4 off

theorem program80Prefix_instruction_count (off : Nat) :
    (program80Prefix off).length = 244 := by
  simp only [program80Prefix, batch0, batch1, batch2, batch3,
    immediateAt, dupAt, lookupDup, squares, squareProgram,
    WindowTwentyOneStage.pairProgram, Lookup.lookupImmediateProgram,
    WindowTwentyOneLookup.program, List.length_append, List.length_cons,
    List.length_nil]
  decide

theorem program80_instruction_count (off : Nat) : (program80 off).length = 309 := by
  simp only [program80, program80Prefix, batch0, batch1, batch2, batch3, batch4,
    immediateAt, dupAt, lookupDup, squares, squareProgram,
    WindowTwentyOneStage.pairProgram, Lookup.lookupImmediateProgram,
    WindowTwentyOneLookup.program, List.length_append, List.length_cons,
    List.length_nil]
  decide

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem laddr_bound (index : Nat) (hindex : index < 62) :
    WindowCopyMemory.laddr index + 32 ≤ 576 := by
  unfold WindowCopyMemory.laddr
  split <;> omega

def blockDigit (exponent : UInt256) (off index : Nat) : Nat :=
  WindowTwentyOneMath.nibble exponent.toNat (1 + off + index)

def blockMemory (mem : ByteArray) (exponent : UInt256) : ByteArray :=
  WindowCopyMemory.copyMem mem (UInt256.shiftLeft exponent (UInt256.ofNat 1))

theorem block_address (mem : ByteArray) (exponent : UInt256)
    (off index : Nat) (hindex : off + index < 62) :
    (UInt256.land (UInt256.ofNat 480)
      (MachineState.readWord
        (blockMemory mem exponent)
      (WindowCopyMemory.laddr (off + index)))).toNat =
      32 * blockDigit exponent off index := by
  change (UInt256.land (UInt256.ofNat 480)
      (MachineState.readWord
        (WindowCopyMemory.copyMem mem
          (UInt256.shiftLeft exponent (UInt256.ofNat 1)))
        (WindowCopyMemory.laddr (off + index)))).toNat =
      32 * blockDigit exponent off index
  have haddr := WindowCopyMemory.land480_laddr mem
    (UInt256.shiftLeft exponent (UInt256.ofNat 1)) (off + index) hindex
  rw [haddr, land_comm]
  have hshift := WindowTwentyOneBits.shifted_lookupAddress exponent 1
    (off + index) (by omega) hindex (by omega)
  rw [show 1 + (off + index) = 1 + off + index by omega] at hshift
  simpa [blockMemory, blockDigit, WindowTwentyOneBits.lookupAddress,
    WindowTwentyOneMath.nibble] using
    hshift

theorem block_table (mem : ByteArray) (exponent base modulus : UInt256)
    (index : Nat) (hindex : index < 16)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i) :
    MachineState.readWord
        (blockMemory mem exponent) (32 * index) =
      WindowMath.tableWord base modulus index := by
  rw [blockMemory, WindowCopyMemory.readWord_copyMem_low _ _ _ (by omega)]
  exact htable index hindex

theorem block_lookupFacts (mem : ByteArray) (exponent base modulus : UInt256)
    (off position : Nat) (hbound : off + position < 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i) :
    blockDigit exponent off position < 16 ∧
      WindowCopyMemory.laddr (off + position) + 32 ≤ 576 ∧
      MachineState.readWord (blockMemory mem exponent)
        (32 * blockDigit exponent off position) =
        WindowMath.tableWord base modulus (blockDigit exponent off position) ∧
      (UInt256.land (UInt256.ofNat 480)
        (MachineState.readWord (blockMemory mem exponent)
          (WindowCopyMemory.laddr (off + position)))).toNat =
        32 * blockDigit exponent off position := by
  have hd : blockDigit exponent off position < 16 := by
    exact WindowTwentyOneMath.nibble_lt _ _
  have htable' := block_table mem exponent base modulus
    (blockDigit exponent off position) hd htable
  have haddress := block_address mem exponent off position hbound
  exact ⟨hd, laddr_bound (off + position) hbound, htable', haddress⟩

theorem squareWordAfter_add (modulus accumulator : UInt256) (left right : Nat) :
    WindowMath.squareWordAfter modulus left
        (WindowMath.squareWordAfter modulus right accumulator) =
      WindowMath.squareWordAfter modulus (left + right) accumulator := by
  induction left generalizing accumulator with
  | zero =>
      simp only [Nat.zero_add]
      rfl
  | succ left ih =>
      simp only [WindowMath.squareWordAfter]
      rw [ih]
      rw [show left + 1 + right = (left + right) + 1 by omega]
      rfl

theorem run_batch0 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 12 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (batch0 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        accumulator (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 69 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowMath.squareWordAfter modulus 1
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 3 accumulator))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let d0 := blockDigit exponent off 0
  let d1 := blockDigit exponent off 1
  let d2 := blockDigit exponent off 2
  let a1 := WindowMath.nibbleWordStep modulus base accumulator d0
  let a2 := WindowMath.nibbleWordStep modulus base a1 d1
  let a3 := WindowMath.nibbleWordStep modulus base a2 d2
  have f0 := block_lookupFacts mem exponent base modulus off 0 (by omega) htable
  have f1 := block_lookupFacts mem exponent base modulus off 1 (by omega) htable
  have f2 := block_lookupFacts mem exponent base modulus off 2 (by omega) htable
  have hs := run_stageAt template pc cm modulus accumulator shifted counter rest hrest
  have hp0 := run_phaseImmediate template (advancePC 17 pc) cm base modulus accumulator
    shifted counter rest 17 4 (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 0)) f0.2.1 d0 f0.1 f0.2.2.1 f0.2.2.2 hrest
  have hp1 := run_phaseDup template (advancePC 35 pc) cm base modulus a1 shifted counter
    rest 12 4 7 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 1)) f1.2.1 d1 f1.1 f1.2.2.1 f1.2.2.2 hrest
  have hp2 := run_phaseDup template (advancePC 51 pc) cm base modulus a2 shifted counter
    rest 7 4 2 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 2)) f2.2.1 d2 f2.1 f2.2.2.1 f2.2.2.2 hrest
  have hsq := run_squares template (advancePC 67 pc) cm 18 modulus a3
    ([modulus, shifted, UInt256.ofNat 480, counter] ++ rest) 1 (by decide) (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hpc0 : advancePC 18 (advancePC 17 pc) = advancePC 35 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 16 (advancePC 35 pc) = advancePC 51 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 16 (advancePC 51 pc) = advancePC 67 pc := by
    rw [← advancePC_add]
  have hpc3 : advancePC 2 (advancePC 67 pc) = advancePC 69 pc := by
    rw [← advancePC_add]
  have hp0' :
      runInstructions (squares 4 ++ Lookup.lookupImmediateProgram
          (WindowCopyMemory.laddr (off + 0)))
        (WindowTwentyOneGroup.state template (advancePC 17 pc) cm 18 modulus
          accumulator shifted counter 16 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 35 pc) cm 18 modulus
        a1 shifted counter 11 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      d0, a1, Lookup.lookupImmediateProgram, hpc0, List.replicate_succ,
      List.replicate_succ', List.cons_append, List.nil_append, List.append_assoc,
      WindowMath.nibbleWordStep] using hp0
  have hp1' :
      runInstructions (squares 4 ++ lookupDup 7
          (WindowCopyMemory.laddr (off + 1)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 35 pc) cm 18 modulus
          a1 shifted counter 11 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 51 pc) cm 18 modulus
        a2 shifted counter 6 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      d1, a1, a2, lookupDup, WindowTwentyOneLookup.program, hpc1,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp1
  have hp2' :
      runInstructions (squares 4 ++ lookupDup 2
          (WindowCopyMemory.laddr (off + 2)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 51 pc) cm 18 modulus
          a2 shifted counter 6 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 67 pc) cm 18 modulus
        a3 shifted counter 1 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      d2, a2, a3, lookupDup, WindowTwentyOneLookup.program, hpc2,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp2
  have hsq' :
      runInstructions (squares 1)
        (WindowTwentyOneGroup.state template (advancePC 67 pc) cm 18 modulus
          a3 shifted counter 1 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 69 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 1 a3) shifted counter 0 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
      cm, shifted, hpc3, List.replicate_succ, List.replicate_succ',
      List.cons_append, List.nil_append, List.append_assoc] using hsq
  have h01 := runInstructions_append_some _ _ _ _ _ hs hp0'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 hp1'
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 hp2'
  have hall := runInstructions_append_some _ _ _ _ _ h0123 hsq'
  have ha3 : a3 = WindowTwentyOneMath.advance base modulus exponent.toNat
      (1 + off) 3 accumulator := by
    simp [a1, a2, a3, d0, d1, d2, blockDigit, WindowTwentyOneMath.advance,
      WindowMath.nibbleWordStep, Nat.add_assoc]
  simpa [batch0, immediateAt, dupAt, lookupDup, WindowTwentyOneLookup.program,
    ha3, cm, shifted, List.append_assoc] using hall

theorem run_batch1 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 12 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (batch1 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        (WindowMath.squareWordAfter modulus 1
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 3 accumulator))
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 69 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowMath.squareWordAfter modulus 2
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let seed := WindowMath.squareWordAfter modulus 1
    (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 3 accumulator)
  let d3 := blockDigit exponent off 3
  let d4 := blockDigit exponent off 4
  let d5 := blockDigit exponent off 5
  let a4 := UInt256.mulMod (WindowMath.squareWordAfter modulus 3 seed)
    (WindowMath.tableWord base modulus d3) modulus
  let a5 := WindowMath.nibbleWordStep modulus base a4 d4
  let a6 := WindowMath.nibbleWordStep modulus base a5 d5
  have f3 := block_lookupFacts mem exponent base modulus off 3 (by omega) htable
  have f4 := block_lookupFacts mem exponent base modulus off 4 (by omega) htable
  have f5 := block_lookupFacts mem exponent base modulus off 5 (by omega) htable
  have hs := run_stageAt template pc cm modulus seed shifted counter rest hrest
  have hp0 := run_phaseImmediate template (advancePC 17 pc) cm base modulus seed
    shifted counter rest 17 3 (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 3)) f3.2.1 d3 f3.1 f3.2.2.1 f3.2.2.2 hrest
  have hp1 := run_phaseDup template (advancePC 33 pc) cm base modulus a4 shifted counter
    rest 13 4 8 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 4)) f4.2.1 d4 f4.1 f4.2.2.1 f4.2.2.2 hrest
  have hp2 := run_phaseDup template (advancePC 49 pc) cm base modulus a5 shifted counter
    rest 8 4 3 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 5)) f5.2.1 d5 f5.1 f5.2.2.1 f5.2.2.2 hrest
  have hsq := run_squares template (advancePC 65 pc) cm 18 modulus a6
    ([modulus, shifted, UInt256.ofNat 480, counter] ++ rest) 2 (by decide) (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hpc0 : advancePC 16 (advancePC 17 pc) = advancePC 33 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 16 (advancePC 33 pc) = advancePC 49 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 16 (advancePC 49 pc) = advancePC 65 pc := by
    rw [← advancePC_add]
  have hpc3 : advancePC 4 (advancePC 65 pc) = advancePC 69 pc := by
    rw [← advancePC_add]
  have hp0' :
      runInstructions (squares 3 ++ Lookup.lookupImmediateProgram
          (WindowCopyMemory.laddr (off + 3)))
        (WindowTwentyOneGroup.state template (advancePC 17 pc) cm 18 modulus
          seed shifted counter 16 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 33 pc) cm 18 modulus
        a4 shifted counter 12 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a4, seed, d3, Lookup.lookupImmediateProgram, hpc0, List.replicate_succ,
      List.replicate_succ', List.cons_append, List.nil_append, List.append_assoc] using hp0
  have hp1' :
      runInstructions (squares 4 ++ lookupDup 8
          (WindowCopyMemory.laddr (off + 4)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 33 pc) cm 18 modulus
          a4 shifted counter 12 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 49 pc) cm 18 modulus
        a5 shifted counter 7 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a4, a5, d4, lookupDup, WindowTwentyOneLookup.program, hpc1,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp1
  have hp2' :
      runInstructions (squares 4 ++ lookupDup 3
          (WindowCopyMemory.laddr (off + 5)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 49 pc) cm 18 modulus
          a5 shifted counter 7 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 65 pc) cm 18 modulus
        a6 shifted counter 2 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a5, a6, d5, lookupDup, WindowTwentyOneLookup.program, hpc2,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp2
  have hsq' :
      runInstructions (squares 2)
        (WindowTwentyOneGroup.state template (advancePC 65 pc) cm 18 modulus
          a6 shifted counter 2 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 69 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 2 a6) shifted counter 0 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
      cm, shifted, hpc3, List.replicate_succ, List.replicate_succ',
      List.cons_append, List.nil_append, List.append_assoc] using hsq
  have h01 := runInstructions_append_some _ _ _ _ _ hs hp0'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 hp1'
  have hall := runInstructions_append_some _ _ _ _ _ h012 hp2'
  have hall' := runInstructions_append_some _ _ _ _ _ hall hsq'
  have ha6 :
      WindowMath.squareWordAfter modulus 2 a6 =
        WindowMath.squareWordAfter modulus 2
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator) := by
    have ha4 : a4 = WindowMath.nibbleWordStep modulus base
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 3 accumulator) d3 := by
      simp [a4, seed, d3, blockDigit, WindowMath.nibbleWordStep,
        squareWordAfter_add]
    simp [a4, a5, a6, d3, d4, d5, blockDigit, ha4,
      WindowMath.nibbleWordStep, WindowTwentyOneMath.advance, Nat.add_assoc]
  simpa [batch1, immediateAt, dupAt, lookupDup, WindowTwentyOneLookup.program,
    ha6, cm, shifted, List.append_assoc] using hall'

theorem run_batch2 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 12 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (batch2 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        (WindowMath.squareWordAfter modulus 2
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator))
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 69 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowMath.squareWordAfter modulus 3
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let seed := WindowMath.squareWordAfter modulus 2
    (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator)
  let d6 := blockDigit exponent off 6
  let d7 := blockDigit exponent off 7
  let d8 := blockDigit exponent off 8
  let a7 := UInt256.mulMod (WindowMath.squareWordAfter modulus 2 seed)
    (WindowMath.tableWord base modulus d6) modulus
  let a8 := WindowMath.nibbleWordStep modulus base a7 d7
  let a9 := WindowMath.nibbleWordStep modulus base a8 d8
  have f6 := block_lookupFacts mem exponent base modulus off 6 (by omega) htable
  have f7 := block_lookupFacts mem exponent base modulus off 7 (by omega) htable
  have f8 := block_lookupFacts mem exponent base modulus off 8 (by omega) htable
  have hs := run_stageAt template pc cm modulus seed shifted counter rest hrest
  have hp0 := run_phaseImmediate template (advancePC 17 pc) cm base modulus seed
    shifted counter rest 17 2 (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 6)) f6.2.1 d6 f6.1 f6.2.2.1 f6.2.2.2 hrest
  have hp1 := run_phaseDup template (advancePC 31 pc) cm base modulus a7 shifted counter
    rest 14 4 9 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 7)) f7.2.1 d7 f7.1 f7.2.2.1 f7.2.2.2 hrest
  have hp2 := run_phaseDup template (advancePC 47 pc) cm base modulus a8 shifted counter
    rest 9 4 4 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 8)) f8.2.1 d8 f8.1 f8.2.2.1 f8.2.2.2 hrest
  have hsq := run_squares template (advancePC 63 pc) cm 18 modulus a9
    ([modulus, shifted, UInt256.ofNat 480, counter] ++ rest) 3 (by decide) (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hpc0 : advancePC 14 (advancePC 17 pc) = advancePC 31 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 16 (advancePC 31 pc) = advancePC 47 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 16 (advancePC 47 pc) = advancePC 63 pc := by
    rw [← advancePC_add]
  have hpc3 : advancePC 6 (advancePC 63 pc) = advancePC 69 pc := by
    rw [← advancePC_add]
  have hp0' :
      runInstructions (squares 2 ++ Lookup.lookupImmediateProgram
          (WindowCopyMemory.laddr (off + 6)))
        (WindowTwentyOneGroup.state template (advancePC 17 pc) cm 18 modulus
          seed shifted counter 16 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 31 pc) cm 18 modulus
        a7 shifted counter 13 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a7, seed, d6, Lookup.lookupImmediateProgram, hpc0, List.replicate_succ,
      List.replicate_succ', List.cons_append, List.nil_append, List.append_assoc] using hp0
  have hp1' :
      runInstructions (squares 4 ++ lookupDup 9
          (WindowCopyMemory.laddr (off + 7)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 31 pc) cm 18 modulus
          a7 shifted counter 13 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 47 pc) cm 18 modulus
        a8 shifted counter 8 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a7, a8, d7, lookupDup, WindowTwentyOneLookup.program, hpc1,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp1
  have hp2' :
      runInstructions (squares 4 ++ lookupDup 4
          (WindowCopyMemory.laddr (off + 8)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 47 pc) cm 18 modulus
          a8 shifted counter 8 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 63 pc) cm 18 modulus
        a9 shifted counter 3 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a8, a9, d8, lookupDup, WindowTwentyOneLookup.program, hpc2,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp2
  have hsq' :
      runInstructions (squares 3)
        (WindowTwentyOneGroup.state template (advancePC 63 pc) cm 18 modulus
          a9 shifted counter 3 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 69 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 3 a9) shifted counter 0 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
      cm, shifted, hpc3, List.replicate_succ, List.replicate_succ',
      List.cons_append, List.nil_append, List.append_assoc] using hsq
  have h01 := runInstructions_append_some _ _ _ _ _ hs hp0'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 hp1'
  have hall := runInstructions_append_some _ _ _ _ _ h012 hp2'
  have hall' := runInstructions_append_some _ _ _ _ _ hall hsq'
  have ha9 :
      WindowMath.squareWordAfter modulus 3 a9 =
        WindowMath.squareWordAfter modulus 3
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator) := by
    have ha7 : a7 = WindowMath.nibbleWordStep modulus base
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator) d6 := by
      simp [a7, seed, d6, blockDigit, WindowMath.nibbleWordStep,
        squareWordAfter_add]
    simp [a7, a8, a9, d6, d7, d8, blockDigit, ha7,
      WindowMath.nibbleWordStep, WindowTwentyOneMath.advance, Nat.add_assoc]
  simpa [batch2, immediateAt, dupAt, lookupDup, WindowTwentyOneLookup.program,
    ha9, cm, shifted, List.append_assoc] using hall'

theorem run_batch3 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 12 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (batch3 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        (WindowMath.squareWordAfter modulus 3
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator))
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 69 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let seed := WindowMath.squareWordAfter modulus 3
    (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator)
  let d9 := blockDigit exponent off 9
  let d10 := blockDigit exponent off 10
  let d11 := blockDigit exponent off 11
  let a10 := UInt256.mulMod (WindowMath.squareWordAfter modulus 1 seed)
    (WindowMath.tableWord base modulus d9) modulus
  let a11 := WindowMath.nibbleWordStep modulus base a10 d10
  let a12 := WindowMath.nibbleWordStep modulus base a11 d11
  have f9 := block_lookupFacts mem exponent base modulus off 9 (by omega) htable
  have f10 := block_lookupFacts mem exponent base modulus off 10 (by omega) htable
  have f11 := block_lookupFacts mem exponent base modulus off 11 (by omega) htable
  have hs := run_stageAt template pc cm modulus seed shifted counter rest hrest
  have hp0 := run_phaseImmediate template (advancePC 17 pc) cm base modulus seed
    shifted counter rest 17 1 (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 9)) f9.2.1 d9 f9.1 f9.2.2.1 f9.2.2.2 hrest
  have hp1 := run_phaseDup template (advancePC 29 pc) cm base modulus a10 shifted counter
    rest 15 4 10 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 10)) f10.2.1 d10 f10.1 f10.2.2.1 f10.2.2.2 hrest
  have hp2 := run_phaseDup template (advancePC 45 pc) cm base modulus a11 shifted counter
    rest 10 4 5 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 11)) f11.2.1 d11 f11.1 f11.2.2.1 f11.2.2.2 hrest
  have hsq := run_squares template (advancePC 61 pc) cm 18 modulus a12
    ([modulus, shifted, UInt256.ofNat 480, counter] ++ rest) 4 (by decide) (by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hpc0 : advancePC 12 (advancePC 17 pc) = advancePC 29 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 16 (advancePC 29 pc) = advancePC 45 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 16 (advancePC 45 pc) = advancePC 61 pc := by
    rw [← advancePC_add]
  have hpc3 : advancePC 8 (advancePC 61 pc) = advancePC 69 pc := by
    rw [← advancePC_add]
  have hp0' :
      runInstructions (squares 1 ++ Lookup.lookupImmediateProgram
          (WindowCopyMemory.laddr (off + 9)))
        (WindowTwentyOneGroup.state template (advancePC 17 pc) cm 18 modulus
          seed shifted counter 16 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 29 pc) cm 18 modulus
        a10 shifted counter 14 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a10, seed, d9, Lookup.lookupImmediateProgram, hpc0, List.replicate_succ,
      List.replicate_succ', List.cons_append, List.nil_append, List.append_assoc] using hp0
  have hp1' :
      runInstructions (squares 4 ++ lookupDup 10
          (WindowCopyMemory.laddr (off + 10)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 29 pc) cm 18 modulus
          a10 shifted counter 14 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 45 pc) cm 18 modulus
        a11 shifted counter 9 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a10, a11, d10, lookupDup, WindowTwentyOneLookup.program, hpc1,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp1
  have hp2' :
      runInstructions (squares 4 ++ lookupDup 5
          (WindowCopyMemory.laddr (off + 11)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 45 pc) cm 18 modulus
          a11 shifted counter 9 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 61 pc) cm 18 modulus
        a12 shifted counter 4 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a11, a12, d11, lookupDup, WindowTwentyOneLookup.program, hpc2,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp2
  have hsq' :
      runInstructions (squares 4)
        (WindowTwentyOneGroup.state template (advancePC 61 pc) cm 18 modulus
          a12 shifted counter 4 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 69 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 4 a12) shifted counter 0 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
      cm, shifted, hpc3, List.replicate_succ, List.replicate_succ',
      List.cons_append, List.nil_append, List.append_assoc] using hsq
  have h01 := runInstructions_append_some _ _ _ _ _ hs hp0'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 hp1'
  have hall := runInstructions_append_some _ _ _ _ _ h012 hp2'
  have hall' := runInstructions_append_some _ _ _ _ _ hall hsq'
  have ha12 :
      WindowMath.squareWordAfter modulus 4 a12 =
        WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator) := by
    have ha10 : a10 = WindowMath.nibbleWordStep modulus base
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator) d9 := by
      simp [a10, seed, d9, blockDigit, WindowMath.nibbleWordStep,
        squareWordAfter_add]
    simp [a10, a11, a12, d9, d10, d11, blockDigit, ha10,
      WindowMath.nibbleWordStep, WindowTwentyOneMath.advance, Nat.add_assoc]
  simpa [batch3, immediateAt, dupAt, lookupDup, WindowTwentyOneLookup.program,
    ha12, cm, shifted, List.append_assoc] using hall'

theorem run_batch4 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 16 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (batch4 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator))
        (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 75 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 16 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let seed := WindowMath.squareWordAfter modulus 4
    (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator)
  let d12 := blockDigit exponent off 12
  let d13 := blockDigit exponent off 13
  let d14 := blockDigit exponent off 14
  let d15 := blockDigit exponent off 15
  let a13 := UInt256.mulMod (WindowMath.squareWordAfter modulus 0 seed)
    (WindowMath.tableWord base modulus d12) modulus
  let a14 := WindowMath.nibbleWordStep modulus base a13 d13
  let a15 := WindowMath.nibbleWordStep modulus base a14 d14
  let a16 := WindowMath.nibbleWordStep modulus base a15 d15
  have f12 := block_lookupFacts mem exponent base modulus off 12 (by omega) htable
  have f13 := block_lookupFacts mem exponent base modulus off 13 (by omega) htable
  have f14 := block_lookupFacts mem exponent base modulus off 14 (by omega) htable
  have f15 := block_lookupFacts mem exponent base modulus off 15 (by omega) htable
  have hs := run_stageAt template pc cm modulus seed shifted counter rest hrest
  have hp0 := run_phaseImmediate template (advancePC 17 pc) cm base modulus seed
    shifted counter rest 17 0 (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 12)) f12.2.1 d12 f12.1 f12.2.2.1 f12.2.2.2 hrest
  have hp1 := run_phaseDup template (advancePC 27 pc) cm base modulus a13 shifted counter
    rest 16 4 11 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 13)) f13.2.1 d13 f13.1 f13.2.2.1 f13.2.2.2 hrest
  have hp2 := run_phaseDup template (advancePC 43 pc) cm base modulus a14 shifted counter
    rest 11 4 6 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 14)) f14.2.1 d14 f14.1 f14.2.2.1 f14.2.2.2 hrest
  have hp3 := run_phaseDup template (advancePC 59 pc) cm base modulus a15 shifted counter
    rest 6 4 1 (by decide) (by decide) (by decide) (by decide)
    (WindowCopyMemory.laddr (off + 15)) f15.2.1 d15 f15.1 f15.2.2.1 f15.2.2.2 hrest
  have hpc0 : advancePC 10 (advancePC 17 pc) = advancePC 27 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 16 (advancePC 27 pc) = advancePC 43 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 16 (advancePC 43 pc) = advancePC 59 pc := by
    rw [← advancePC_add]
  have hpc3 : advancePC 16 (advancePC 59 pc) = advancePC 75 pc := by
    rw [← advancePC_add]
  have hp0' :
      runInstructions (Lookup.lookupImmediateProgram
          (WindowCopyMemory.laddr (off + 12)))
        (WindowTwentyOneGroup.state template (advancePC 17 pc) cm 18 modulus
          seed shifted counter 16 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 27 pc) cm 18 modulus
        a13 shifted counter 15 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a13, seed, d12, squares, Lookup.lookupImmediateProgram, hpc0, List.replicate_succ,
      List.replicate_succ', List.cons_append, List.nil_append, List.append_assoc] using hp0
  have hp1' :
      runInstructions (squares 4 ++ lookupDup 11
          (WindowCopyMemory.laddr (off + 13)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 27 pc) cm 18 modulus
          a13 shifted counter 15 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 43 pc) cm 18 modulus
        a14 shifted counter 10 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a13, a14, d13, lookupDup, WindowTwentyOneLookup.program, hpc1,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp1
  have hp2' :
      runInstructions (squares 4 ++ lookupDup 6
          (WindowCopyMemory.laddr (off + 14)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 43 pc) cm 18 modulus
          a14 shifted counter 10 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 59 pc) cm 18 modulus
        a15 shifted counter 5 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a14, a15, d14, lookupDup, WindowTwentyOneLookup.program, hpc2,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp2
  have hp3' :
      runInstructions (squares 4 ++ lookupDup 1
          (WindowCopyMemory.laddr (off + 15)) (by decide))
        (WindowTwentyOneGroup.state template (advancePC 59 pc) cm 18 modulus
          a15 shifted counter 5 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 75 pc) cm 18 modulus
        a16 shifted counter 0 rest) := by
    simpa [WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed, cm, shifted,
      a15, a16, d15, lookupDup, WindowTwentyOneLookup.program, hpc3,
      List.replicate_succ, List.replicate_succ', List.cons_append, List.nil_append,
      List.append_assoc, WindowMath.nibbleWordStep] using hp3
  have h01 := runInstructions_append_some _ _ _ _ _ hs hp0'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 hp1'
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 hp2'
  have hall := runInstructions_append_some _ _ _ _ _ h0123 hp3'
  have ha16 : a16 = WindowTwentyOneMath.advance base modulus exponent.toNat
      (1 + off) 16 accumulator := by
    simp [a13, a14, a15, a16, d12, d13, d14, d15, blockDigit, seed,
      WindowMath.nibbleWordStep, WindowTwentyOneMath.advance,
      WindowMath.squareWordAfter, Nat.add_assoc]
  simpa [batch4, immediateAt, dupAt, lookupDup, WindowTwentyOneLookup.program,
    ha16, cm, shifted, List.append_assoc] using hall

theorem run_program80Prefix (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 12 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program80Prefix off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        accumulator (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 276 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowMath.squareWordAfter modulus 4
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator))
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let a3 := WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 3 accumulator
  let a6 := WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 6 accumulator
  let a9 := WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 9 accumulator
  have h0 := run_batch0 template pc mem base modulus exponent accumulator counter off hoff
    htable rest hrest
  have h1 := run_batch1 template (advancePC 69 pc) mem base modulus exponent
    accumulator counter off hoff htable rest hrest
  have h2 := run_batch2 template (advancePC 138 pc) mem base modulus exponent
    accumulator counter off hoff htable rest hrest
  have h3 := run_batch3 template (advancePC 207 pc) mem base modulus exponent
    accumulator counter off hoff htable rest hrest
  have hpc0 : advancePC 69 (advancePC 69 pc) = advancePC 138 pc := by
    rw [← advancePC_add]
  have hpc1 : advancePC 69 (advancePC 138 pc) = advancePC 207 pc := by
    rw [← advancePC_add]
  have hpc2 : advancePC 69 (advancePC 207 pc) = advancePC 276 pc := by
    rw [← advancePC_add]
  have h1' :
      runInstructions (batch1 off)
        (WindowTwentyOneGroup.state template (advancePC 69 pc) cm 18 modulus
          (WindowMath.squareWordAfter modulus 1 a3) shifted counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 138 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 2 a6) shifted counter 0 rest) := by
    simpa [cm, shifted, hpc0] using h1
  have h2' :
      runInstructions (batch2 off)
        (WindowTwentyOneGroup.state template (advancePC 138 pc) cm 18 modulus
          (WindowMath.squareWordAfter modulus 2 a6) shifted counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 207 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 3 a9) shifted counter 0 rest) := by
    simpa [cm, shifted, hpc1] using h2
  have h3' :
      runInstructions (batch3 off)
        (WindowTwentyOneGroup.state template (advancePC 207 pc) cm 18 modulus
          (WindowMath.squareWordAfter modulus 3 a9) shifted counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 276 pc) cm 18 modulus
        (WindowMath.squareWordAfter modulus 4
          (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator))
        shifted counter 0 rest) := by
    simpa [cm, shifted, hpc2] using h3
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1'
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2'
  have hall := runInstructions_append_some _ _ _ _ _ h012 h3'
  simpa [program80Prefix, cm, shifted, List.append_assoc] using hall

theorem run_program80 (template : State) (pc : UInt256) (mem : ByteArray)
    (base modulus exponent accumulator counter : UInt256) (off : Nat)
    (hoff : off + 16 ≤ 62)
    (htable : ∀ i, i < 16 →
      MachineState.readWord mem (32 * i) = WindowMath.tableWord base modulus i)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (program80 off)
      (WindowTwentyOneGroup.state template pc (blockMemory mem exponent) 18 modulus
        accumulator (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 351 pc)
      (blockMemory mem exponent) 18 modulus
      (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 16 accumulator)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) counter 0 rest) := by
  let shifted := UInt256.shiftLeft exponent (UInt256.ofNat 1)
  let cm := blockMemory mem exponent
  let a12 := WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 12 accumulator
  have hp := run_program80Prefix template pc mem base modulus exponent accumulator counter off
    (by omega) htable rest hrest
  have h4 := run_batch4 template (advancePC 276 pc) mem base modulus exponent
    accumulator counter off hoff htable rest hrest
  have hpc : advancePC 75 (advancePC 276 pc) = advancePC 351 pc := by
    rw [← advancePC_add]
  have h4' :
      runInstructions (batch4 off)
        (WindowTwentyOneGroup.state template (advancePC 276 pc) cm 18 modulus
          (WindowMath.squareWordAfter modulus 4 a12) shifted counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC 351 pc) cm 18 modulus
        (WindowTwentyOneMath.advance base modulus exponent.toNat (1 + off) 16 accumulator)
        shifted counter 0 rest) := by
    simpa [cm, shifted, hpc] using h4
  have hall := runInstructions_append_some _ _ _ _ _ hp h4'
  simpa [program80, program80Prefix, cm, shifted, List.append_assoc] using hall

end Block

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBlock

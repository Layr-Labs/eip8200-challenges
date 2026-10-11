import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def cleanProgram : List Instr := [.push 2 480]

def addressProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 247, .op .SHR,
   .op (.Dup ⟨1, by decide⟩), .op .AND]

def lookupProgram : List Instr := cleanProgram ++ addressProgram ++ [.op .MLOAD]

def address (exponent : UInt256) : UInt256 :=
  UInt256.land (UInt256.ofNat 480) (UInt256.shiftRight exponent (UInt256.ofNat 247))

private theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem first_address (exponent : UInt256) :
    (UInt256.land (UInt256.ofNat 480)
      (UInt256.shiftRight exponent (UInt256.ofNat 247))).toNat =
      32 * WindowTwentyOneMath.nibble exponent.toNat 0 := by
  rw [land_comm]
  have h := WindowTwentyOneBits.lookupAddress_toNat exponent 247 (by decide)
  simpa only [WindowTwentyOneBits.lookupAddress, WindowTwentyOneMath.nibble,
    Nat.shiftRight_eq_div_pow, show 247 + 5 = 252 by decide,
    show (2 : Nat) ^ 252 = 16 ^ 63 by decide] using h

private theorem run_clean (template : State) (pc base modulus : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1010) :
    runInstructions cleanProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 rest) =
    some (WindowTwentyOneTable.framed template (advancePC 3 pc) base modulus 16
      (UInt256.ofNat 480 :: rest)) := by
  have hcap1 : rest.length < 1024 := by omega
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + (UInt256.ofNat 1 + UInt256.ofNat 1) := by decide
  simp [runInstructions, cleanProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap1,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp3, word_add_assoc]

private theorem run_address (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions addressProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([UInt256.ofNat 480, modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 6 pc) base modulus 16
      ([address exponent, UInt256.ofNat 480, modulus, exponent] ++ rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, addressProgram, address, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_load (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op .MLOAD]
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([address exponent, UInt256.ofNat 480, modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template pc.succ base modulus 16
      ([WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat,
        UInt256.ofNat 480, modulus, exponent] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hread : MachineState.readWord (WindowTableMemory.tableMemoryThrough base modulus 16)
      (32 * WindowTwentyOneMath.nibble exponent.toNat 0) =
      WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 0) :=
    WindowTableMemory.readWord_tableMemory base modulus
      (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  have hactive := WindowTableMemory.activeWordsAfter_lookup
    (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  simp [runInstructions, address, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, Nat.add_assoc, first_address, hread, hactive,
    WindowTwentyOneMath.initialAccumulator, State.activeWordsAfterUInt256]

theorem run_lookup (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions lookupProgram
      (WindowTwentyOneTable.framed template pc base modulus 16 ([modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 10 pc) base modulus 16
      ([WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat,
        UInt256.ofNat 480, modulus, exponent] ++ rest)) := by
  have hc := run_clean template pc base modulus ([modulus, exponent] ++ rest)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have ha := run_address template (advancePC 3 pc) base modulus exponent rest hrest
  have hl := run_load template (advancePC 6 (advancePC 3 pc)) base modulus exponent rest hrest
  have hca := runInstructions_append_some _ _ _ _ _ hc ha
  have hall := runInstructions_append_some _ _ _ _ _ hca hl
  have hpc : (advancePC 6 (advancePC 3 pc)).succ = advancePC 10 pc := rfl
  simpa only [lookupProgram, List.cons_append, hpc] using hall

def frameArrangeProgram : List Instr :=
  [.op (.Swap ⟨2, by decide⟩), .push 1 1, .op .SHL]

def frameLoadProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩)]

def frameProgram : List Instr := frameArrangeProgram ++ frameLoadProgram

private theorem run_arrange (template : State) (pc base modulus exponent accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions frameArrangeProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([accumulator, UInt256.ofNat 480, modulus, exponent] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 4 pc) base modulus 16
      ([UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480,
        modulus, accumulator] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, frameArrangeProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, hcap5, Nat.add_assoc,
    List.exchange, Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_frameLoad (template : State)
    (pc base modulus exponent accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions frameLoadProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([UInt256.shiftLeft exponent (UInt256.ofNat 1), UInt256.ofNat 480,
          modulus, accumulator] ++ rest)) =
    some (WindowTwentyOneTable.framed template (advancePC 3 pc) base modulus 16
      ([accumulator, modulus, UInt256.shiftLeft exponent (UInt256.ofNat 1),
        UInt256.ofNat 480, accumulator] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  simp [runInstructions, frameLoadProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, Nat.add_assoc,
    List.exchange, advancePC, succ_eq_add, word_add_assoc]

theorem run_frame (template : State) (pc base modulus exponent accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions frameProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        ([accumulator, UInt256.ofNat 480, modulus, exponent] ++ rest)) =
    some (WindowTwentyOneGroup.state template (advancePC 7 pc) (WindowTableMemory.tableMemory base modulus) 16 modulus accumulator
      (UInt256.shiftLeft exponent (UInt256.ofNat 1)) accumulator 0 rest) := by
  have ha := run_arrange template pc base modulus exponent accumulator rest hrest
  have hl := run_frameLoad template (advancePC 4 pc) base modulus exponent
    accumulator rest hrest
  have both := runInstructions_append_some _ _ _ _ _ ha hl
  simpa only [frameProgram, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowTwentyOneTable.framed, WindowTableMemory.tableMemory, List.replicate_zero,
    List.nil_append, List.cons_append, ← advancePC_add, show 4 + 3 = 7 by decide] using both

def program : List Instr := lookupProgram ++ frameProgram

theorem run_enter (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 968) base modulus 16 ([modulus, exponent] ++ rest)) =
    some (WindowTwentyOneGroup.state template (UInt256.ofNat 985) (WindowTableMemory.tableMemory base modulus) 16 modulus
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat)
      (UInt256.shiftLeft exponent (UInt256.ofNat 1))
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat) 0 rest) := by
  have hl := run_lookup template (UInt256.ofNat 968) base modulus exponent rest hrest
  have hf := run_frame template (advancePC 10 (UInt256.ofNat 968)) base modulus exponent
    (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat) rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : advancePC 7 (advancePC 10 (UInt256.ofNat 968)) = UInt256.ofNat 985 := by decide
  rw [hpc] at both
  simpa only [program] using both

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

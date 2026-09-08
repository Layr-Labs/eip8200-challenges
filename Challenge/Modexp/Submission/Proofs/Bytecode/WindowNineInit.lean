import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineTable
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineInit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def cleanProgram : List Instr := [.op .POP, .op .POP, .push 2 480]

def addressProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 1 247, .op .SHR,
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
      32 * WindowNineMath.nibble exponent.toNat 0 := by
  rw [land_comm]
  have h := WindowNineBits.lookupAddress_toNat exponent 247 (by decide)
  simpa only [WindowNineBits.lookupAddress, WindowNineMath.nibble,
    Nat.shiftRight_eq_div_pow, show 247 + 5 = 252 by decide,
    show (2 : Nat) ^ 252 = 16 ^ 63 by decide] using h

private theorem run_clean (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions cleanProgram (WindowNineTable.state template pc base modulus exponent 15 rest) =
    some (WindowNineTable.framed template (advancePC 5 pc) base modulus 16
      ([UInt256.ofNat 480, exponent] ++ rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, cleanProgram, WindowNineTable.state, WindowNineTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap1, hcap2, hcap3, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp3, word_add_assoc]

private theorem run_address (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions addressProgram
      (WindowNineTable.framed template pc base modulus 16 ([UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowNineTable.framed template (advancePC 6 pc) base modulus 16
      ([address exponent, UInt256.ofNat 480, exponent] ++ rest)) := by
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, addressProgram, address, WindowNineTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap2, hcap3, hcap4, Nat.add_assoc,
    Challenge.EvmProof.Word.literal_eq_ofNat, advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_load (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op .MLOAD]
      (WindowNineTable.framed template pc base modulus 16
        ([address exponent, UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowNineTable.framed template pc.succ base modulus 16
      ([WindowNineMath.initialAccumulator base modulus exponent.toNat,
        UInt256.ofNat 480, exponent] ++ rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hread : MachineState.readWord (WindowTableMemory.tableMemoryThrough base modulus 16)
      (32 * WindowNineMath.nibble exponent.toNat 0) =
      WindowMath.tableWord base modulus (WindowNineMath.nibble exponent.toNat 0) :=
    WindowTableMemory.readWord_tableMemory base modulus
      (WindowNineMath.nibble exponent.toNat 0) (WindowNineMath.nibble_lt _ _)
  have hactive := WindowTableMemory.activeWordsAfter_lookup
    (WindowNineMath.nibble exponent.toNat 0) (WindowNineMath.nibble_lt _ _)
  simp [runInstructions, address, WindowNineTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap3, Nat.add_assoc, first_address, hread, hactive,
    WindowNineMath.initialAccumulator, State.activeWordsAfterUInt256]

theorem run_lookup (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions lookupProgram (WindowNineTable.state template pc base modulus exponent 15 rest) =
    some (WindowNineTable.framed template (advancePC 12 pc) base modulus 16
      ([WindowNineMath.initialAccumulator base modulus exponent.toNat,
        UInt256.ofNat 480, exponent] ++ rest)) := by
  have hc := run_clean template pc base modulus exponent rest hrest
  have ha := run_address template (advancePC 5 pc) base modulus exponent rest hrest
  have hl := run_load template (advancePC 6 (advancePC 5 pc)) base modulus exponent rest hrest
  have hca := runInstructions_append_some _ _ _ _ _ hc ha
  have hall := runInstructions_append_some _ _ _ _ _ hca hl
  have hpc : (advancePC 6 (advancePC 5 pc)).succ = advancePC 12 pc := rfl
  simpa only [lookupProgram, hpc] using hall

def frameArrangeProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .push 1 4, .op .SHL, .push 1 6,
   .op (.Swap ⟨2, by decide⟩)]

def frameLoadProgram : List Instr :=
  [.op (.Dup ⟨9, by decide⟩), .op .CALLDATALOAD, .op (.Swap ⟨0, by decide⟩)]

def frameProgram : List Instr := frameArrangeProgram ++ frameLoadProgram

private theorem run_arrange (template : State) (pc base modulus exponent accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions frameArrangeProgram
      (WindowNineTable.framed template pc base modulus 16
        ([accumulator, UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowNineTable.framed template (advancePC 7 pc) base modulus 16
      ([accumulator, UInt256.shiftLeft exponent (UInt256.ofNat 4),
        UInt256.ofNat 480, UInt256.ofNat 6] ++ rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, frameArrangeProgram, WindowNineTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, Nat.add_assoc,
    List.exchange, Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc]

private theorem run_frameLoad (template : State)
    (pc base modulus exponent modulusOffset accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus) :
    runInstructions frameLoadProgram
      (WindowNineTable.framed template pc base modulus 16
        ([accumulator, UInt256.shiftLeft exponent (UInt256.ofNat 4),
          UInt256.ofNat 480, UInt256.ofNat 6] ++ rest)) =
    some (WindowNineTable.framed template (advancePC 3 pc) base modulus 16
      ([accumulator, modulus, UInt256.shiftLeft exponent (UInt256.ofNat 4),
        UInt256.ofNat 480, UInt256.ofNat 6] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, frameLoadProgram, WindowNineTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, hcap5, Nat.add_assoc,
    List.getElem?_cons_succ, hoffset, hmodulus, List.exchange, advancePC]

theorem run_frame (template : State) (pc base modulus exponent modulusOffset accumulator : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus) :
    runInstructions frameProgram
      (WindowNineTable.framed template pc base modulus 16
        ([accumulator, UInt256.ofNat 480, exponent] ++ rest)) =
    some (WindowNineGroup.state template (advancePC 10 pc) base modulus accumulator
      (UInt256.shiftLeft exponent (UInt256.ofNat 4)) (UInt256.ofNat 6) 0 rest) := by
  have ha := run_arrange template pc base modulus exponent accumulator rest hrest
  have hl := run_frameLoad template (advancePC 7 pc) base modulus exponent modulusOffset
    accumulator rest hrest hoffset hmodulus
  have both := runInstructions_append_some _ _ _ _ _ ha hl
  simpa only [frameProgram, WindowNineGroup.state, WindowNineLookup.framed,
    WindowNineTable.framed, WindowTableMemory.tableMemory, List.replicate_zero,
    List.nil_append, List.cons_append, ← advancePC_add, show 7 + 3 = 10 by decide] using both

def program : List Instr := lookupProgram ++ frameProgram

theorem run_enter (template : State) (base modulus exponent modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus) :
    runInstructions program
      (WindowNineTable.state template (UInt256.ofNat 2799) base modulus exponent 15 rest) =
    some (WindowNineGroup.state template (UInt256.ofNat 2821) base modulus
      (WindowNineMath.initialAccumulator base modulus exponent.toNat)
      (UInt256.shiftLeft exponent (UInt256.ofNat 4)) (UInt256.ofNat 6) 0 rest) := by
  have hl := run_lookup template (UInt256.ofNat 2799) base modulus exponent rest hrest
  have hf := run_frame template (advancePC 12 (UInt256.ofNat 2799)) base modulus exponent modulusOffset
    (WindowNineMath.initialAccumulator base modulus exponent.toNat) rest hrest hoffset hmodulus
  have both := runInstructions_append_some _ _ _ _ _ hl hf
  have hpc : advancePC 10 (advancePC 12 (UInt256.ofNat 2799)) = UInt256.ofNat 2821 := by decide
  simpa only [program, hpc] using both

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineInit

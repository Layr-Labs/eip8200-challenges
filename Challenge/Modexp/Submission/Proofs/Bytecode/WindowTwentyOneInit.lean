import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTable
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBits
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMath

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-! # The loop frame prologue at 1873

The table build now leaves the bare route stack: its closing `MULMOD` consumed
the `base` and the `modulus` that used to be handed on.  These thirty-one bytes
rebuild the loop frame from scratch — counter, mask, the exponent shifted left
one bit, the modulus, and the first table lookup — and land on the unchanged
trampoline anchor at 1904.

The exponent load that used to sit in the table prelude lives here now. -/

/-- Counter, mask, and the exponent shifted left one bit.  Twenty-one bytes. -/
def framePrepProgram : List Instr :=
  [.push 1 2, .push 13 480, .op (.Dup ⟨6, by decide⟩), .op .CALLDATALOAD,
   .push 1 1, .op .SHL]

/-- The modulus reload.  Two bytes. -/
def modulusLoadProgram : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .CALLDATALOAD]

/-- The first table address: the exponent's top nibble, masked with 480.
Seven bytes. -/
def addressProgram : List Instr :=
  [.op (.Dup ⟨8, by decide⟩), .op .CALLDATALOAD, .push 1 247, .op .SHR,
   .op (.Dup ⟨3, by decide⟩), .op .AND]

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

def program : List Instr :=
  framePrepProgram ++ modulusLoadProgram ++ addressProgram ++ [.op .MLOAD]

private theorem run_framePrep (template : State) (base modulus exponentOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[4]? = some exponentOffset) :
    runInstructions framePrepProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1874) base modulus 16 rest) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 1895) base modulus 16
      ([UInt256.shiftLeft
          (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
          (UInt256.ofNat 1),
        UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  simp [runInstructions, framePrepProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1, hcap2, hcap3, Nat.add_assoc,
    List.getElem?_cons_succ, hoffset,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  omega

private theorem run_modulusLoad (template : State)
    (base modulus exponentShifted modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus) :
    runInstructions modulusLoadProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1895) base modulus 16
        ([exponentShifted, UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 1897) base modulus 16
      ([modulus, exponentShifted, UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  simp [runInstructions, modulusLoadProgram, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, Nat.add_assoc,
    List.getElem?_cons_succ, hoffset, hmodulus,
    Challenge.EvmProof.Word.succ_ofNat_mod]

private theorem run_address (template : State)
    (base modulus exponent exponentShifted exponentOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hoffset : rest[4]? = some exponentOffset)
    (hexponent : MachineState.readWord template.executionEnv.calldata exponentOffset.toNat = exponent) :
    runInstructions addressProgram
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1897) base modulus 16
        ([modulus, exponentShifted, UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) =
    some (WindowTwentyOneTable.framed template (UInt256.ofNat 1904) base modulus 16
      ([address exponent, modulus, exponentShifted, UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, addressProgram, address, WindowTwentyOneTable.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap4, hcap5, hcap6, Nat.add_assoc,
    List.getElem?_cons_succ, hoffset, hexponent,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

private theorem run_mload (template : State)
    (base modulus exponent exponentShifted : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions [.op .MLOAD]
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1904) base modulus 16
        ([address exponent, modulus, exponentShifted, UInt256.ofNat 480, UInt256.ofNat 2] ++ rest)) =
    some (WindowTwentyOneGroup.state template (UInt256.ofNat 1905)
      (WindowTableMemory.tableMemory base modulus) 16 modulus
      (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat)
      exponentShifted (UInt256.ofNat 2) 0 rest) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hread : MachineState.readWord (WindowTableMemory.tableMemoryThrough base modulus 16)
      (32 * WindowTwentyOneMath.nibble exponent.toNat 0) =
      WindowMath.tableWord base modulus (WindowTwentyOneMath.nibble exponent.toNat 0) :=
    WindowTableMemory.readWord_tableMemory base modulus
      (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  have hactive := WindowTableMemory.activeWordsAfter_lookup
    (WindowTwentyOneMath.nibble exponent.toNat 0) (WindowTwentyOneMath.nibble_lt _ _)
  simp [runInstructions, address, WindowTwentyOneTable.framed,
    WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowTableMemory.tableMemory, List.replicate_zero, List.nil_append, List.cons_append,
    Challenge.EvmProof.Stepper.runInstr, hcap5, Nat.add_assoc, first_address, hread, hactive,
    WindowTwentyOneMath.initialAccumulator, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod]

/-- The prologue lands exactly on the unchanged trampoline anchor at 1904. -/
theorem run_enter (template : State) (base modulus exponentOffset modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (he : rest[4]? = some exponentOffset)
    (hm : rest[5]? = some modulusOffset)
    (hmodulus : MachineState.readWord template.executionEnv.calldata modulusOffset.toNat = modulus) :
    runInstructions program
      (WindowTwentyOneTable.framed template (UInt256.ofNat 1874) base modulus 16 rest) =
    some (WindowTwentyOneGroup.state template (UInt256.ofNat 1905)
      (WindowTableMemory.tableMemory base modulus) 16 modulus
      (WindowTwentyOneMath.initialAccumulator base modulus
        (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat).toNat)
      (UInt256.shiftLeft
        (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
        (UInt256.ofNat 1))
      (UInt256.ofNat 2) 0 rest) := by
  let exponent := MachineState.readWord template.executionEnv.calldata exponentOffset.toNat
  have hf := run_framePrep template base modulus exponentOffset rest hrest he
  have hl := run_modulusLoad template base modulus
    (UInt256.shiftLeft exponent (UInt256.ofNat 1)) modulusOffset rest hrest hm hmodulus
  have ha := run_address template base modulus exponent
    (UInt256.shiftLeft exponent (UInt256.ofNat 1)) exponentOffset rest hrest he rfl
  have hd := run_mload template base modulus exponent
    (UInt256.shiftLeft exponent (UInt256.ofNat 1)) rest hrest
  have hfl := runInstructions_append_some _ _ _ _ _ hf hl
  have hfla := runInstructions_append_some _ _ _ _ _ hfl ha
  have hall := runInstructions_append_some _ _ _ _ _ hfla hd
  simpa only [program, exponent, List.append_assoc] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

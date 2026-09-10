import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

def program : List Instr :=
  [.push 0 0, .op .MSTORE, .push 1 32, .push 0 0, .op .RETURN]

def returned (template : State) (pc word : UInt256) (active : Nat)
    (rest : List UInt256) : State :=
  { template with
    pc := pc
    stack := rest
    memory := WindowTableMemory.storeWord template.memory 0 word
    activeWords := UInt256.ofNat (max active 1)
    halt := .Returned
    hReturn := MachineState.readPadded
      (WindowTableMemory.storeWord template.memory 0 word) 0 32 }

theorem run_return (template : State) (pc word : UInt256)
    (active : Nat) (hsmall : active ≤ 16) (hactive : template.activeWords = UInt256.ofNat active)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024) :
    runInstructions program (framed template pc (word :: rest)) =
    some (returned template (advancePC 5 pc) word active rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hm : (UInt256.ofNat (max active 1)).toNat = max active 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, program, framed, returned, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap2, hzero, hactive, ha, hm, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc]

theorem returned_result (template : State) (pc word : UInt256)
    (active : Nat) (rest : List UInt256) :
    (returned template pc word active rest).toResult =
      .returned (Precompile.natToBytes word.toNat 32) := by
  change ExecutionResult.returned
      (MachineState.readPadded (WindowTableMemory.storeWord template.memory 0 word) 0 32) = _
  rw [WindowTableMemory.readPadded_storeWord]
  rfl

def emptyValue (exponent modulus : UInt256) : UInt256 :=
  UInt256.mul (UInt256.mod (UInt256.ofNat 1) modulus) (UInt256.isZero exponent)

def emptyValueProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD, .op .ISZERO,
   .op (.Dup ⟨6, by decide⟩), .op .CALLDATALOAD, .push 1 1, .op .MOD, .op .AND]

private theorem one_mod_toNat (modulus : UInt256) :
    (UInt256.mod (UInt256.ofNat 1) modulus).toNat =
      if modulus.toNat = 0 then 0 else 1 % modulus.toNat := by
  change (if modulus.toNat = 0 then (0 : UInt256)
    else UInt256.mk ((UInt256.ofNat 1).val % modulus.val)).toNat = _
  by_cases hzero : modulus.toNat = 0
  · rw [if_pos hzero, if_pos hzero]
    rfl
  · rw [if_neg hzero, if_neg hzero]
    change ((UInt256.ofNat 1).val % modulus.val).val = _
    rw [Fin.mod_val]
    rfl

private theorem one_mod_le_one (modulus : UInt256) :
    (UInt256.mod (UInt256.ofNat 1) modulus).toNat ≤ 1 := by
  rw [one_mod_toNat]
  by_cases hzero : modulus.toNat = 0
  · simp [hzero]
  · rw [if_neg hzero]
    exact Nat.mod_le _ _

private theorem isZero_le_one (word : UInt256) :
    (UInt256.isZero word).toNat ≤ 1 := by
  rw [Challenge.EvmProof.Word.word_toNat_isZero]
  split <;> omega

private theorem mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem land_mul_of_bits (a b : UInt256)
    (ha : a.toNat ≤ 1) (hb : b.toNat ≤ 1) :
    UInt256.land a b = UInt256.mul a b := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land, mul_toNat]
  have hA : a.toNat = 0 ∨ a.toNat = 1 := by omega
  have hB : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    simp_all <;> norm_num

theorem run_empty_value (template : State) (pc exponentOffset modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset) :
    runInstructions emptyValueProgram (framed template pc rest) =
    some (framed template (advancePC 10 pc)
      (emptyValue (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
        (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat) :: rest)) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hvalue :
      UInt256.land
          (UInt256.mod (UInt256.ofNat 1)
            (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat))
          (UInt256.isZero
            (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)) =
        emptyValue
          (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
          (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat) := by
    unfold emptyValue
    exact land_mul_of_bits _ _
      (one_mod_le_one _)
      (isZero_le_one _)
  simp [runInstructions, emptyValueProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1, hcap2, hcap3,
    List.getElem?_cons_succ, he, hm, Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc, hvalue] <;> rfl

def emptyProgram : List Instr := emptyValueProgram ++ program

theorem run_empty (template : State) (exponentOffset modulusOffset : UInt256)
    (active : Nat) (hsmall : active ≤ 16) (hactive : template.activeWords = UInt256.ofNat active)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset) :
    runInstructions emptyProgram (framed template (UInt256.ofNat 3298) rest) =
    some (returned template (UInt256.ofNat 3313)
      (emptyValue (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
        (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat)) active rest) := by
  let word := emptyValue (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
    (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat)
  have hv := run_empty_value template (UInt256.ofNat 3298) exponentOffset modulusOffset rest hrest he hm
  have hr := run_return template (advancePC 10 (UInt256.ofNat 3298)) word active hsmall hactive rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hv hr
  have hpc : advancePC 5 (advancePC 10 (UInt256.ofNat 3298)) = UInt256.ofNat 3313 := by decide
  simpa only [emptyProgram, hpc, word] using both

def zeroProgram : List Instr := [.op .JUMPDEST, .push 0 0] ++ program

theorem run_zero (template : State) (active : Nat) (hsmall : active ≤ 16)
    (hactive : template.activeWords = UInt256.ofNat active)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024) :
    runInstructions zeroProgram (framed template (UInt256.ofNat 3290) rest) =
    some (returned template (UInt256.ofNat 3297) (UInt256.ofNat 0) active rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hp : runInstructions [.op .JUMPDEST, .push 0 0]
      (framed template (UInt256.ofNat 3290) rest) =
      some (framed template (UInt256.ofNat 3292) (UInt256.ofNat 0 :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap0, hz,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have hr := run_return template (UInt256.ofNat 3292) (UInt256.ofNat 0) active hsmall hactive rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hp hr
  have hpc : advancePC 5 (UInt256.ofNat 3292) = UInt256.ofNat 3297 := by decide
  simpa only [zeroProgram, hpc] using both

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn

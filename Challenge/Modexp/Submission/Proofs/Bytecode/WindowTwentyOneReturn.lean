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

/-- `1 % x` is the `1 < x` predicate: `0` for `x ∈ {0, 1}`, `1` otherwise. -/
private theorem lt_one_eq_mod_one (x : UInt256) :
    UInt256.lt (UInt256.ofNat 1) x = UInt256.ofNat 1 % x := by
  by_cases h0 : x.toNat = 0
  · have hx : x = UInt256.ofNat 0 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h0)
    subst hx
    decide
  by_cases h1 : x.toNat = 1
  · have hx : x = UInt256.ofNat 1 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h1)
    subst hx
    decide
  by_cases h2 : x.toNat = 2
  · have hx : x = UInt256.ofNat 2 :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat x).trans
        (congrArg UInt256.ofNat h2)
    subst hx
    decide
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lt]
  have _h1t : (UInt256.ofNat 1).toNat = 1 := by decide
  rw [if_pos (by omega : (UInt256.ofNat 1).toNat < x.toNat)]
  change (1 : Nat) =
    (if x.toNat = 0 then (0 : UInt256) else
      UInt256.mk ((UInt256.ofNat 1).val % x.val)).toNat
  rw [if_neg h0]
  show (1 : Nat) = ((UInt256.ofNat 1).val % x.val).val
  rw [Fin.mod_val]
  have _hxv : x.val.val > 2 := by
    have h' : x.toNat > 2 := by omega
    exact h'
  rw [Fin.val_ofNat,
    Nat.mod_eq_of_lt (by decide : (1 : Nat) < UInt256.size),
    Nat.mod_eq_of_lt (by omega : (1 : Nat) < x.val.val)]

def emptyValue (exponent modulus : UInt256) : UInt256 :=
  UInt256.mul (UInt256.mod (UInt256.ofNat 1) modulus) (UInt256.isZero exponent)

def emptyValueProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD, .op .ISZERO,
   .op (.Dup ⟨6, by decide⟩), .op .CALLDATALOAD, .push 1 1, .op .LT, .op .MUL]

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
  simp [runInstructions, emptyValueProgram, framed, emptyValue,
    Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1, hcap2, hcap3,
    List.getElem?_cons_succ, he, hm, Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hp2, word_add_assoc, lt_one_eq_mod_one]
  try rfl

def emptyProgram : List Instr := emptyValueProgram ++ program

theorem run_empty (template : State) (exponentOffset modulusOffset : UInt256)
    (active : Nat) (hsmall : active ≤ 16) (hactive : template.activeWords = UInt256.ofNat active)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024)
    (he : rest[4]? = some exponentOffset) (hm : rest[5]? = some modulusOffset) :
    runInstructions emptyProgram (framed template (UInt256.ofNat 3007) rest) =
    some (returned template (UInt256.ofNat 3022)
      (emptyValue (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
        (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat)) active rest) := by
  let word := emptyValue (MachineState.readWord template.executionEnv.calldata exponentOffset.toNat)
    (MachineState.readWord template.executionEnv.calldata modulusOffset.toNat)
  have hv := run_empty_value template (UInt256.ofNat 3007) exponentOffset modulusOffset rest hrest he hm
  have hr := run_return template (advancePC 10 (UInt256.ofNat 3007)) word active hsmall hactive rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hv hr
  have hpc : advancePC 5 (advancePC 10 (UInt256.ofNat 3007)) = UInt256.ofNat 3022 := by decide
  simpa only [emptyProgram, hpc, word] using both

def zeroProgram : List Instr := [.op .JUMPDEST, .push 0 0] ++ program

theorem run_zero (template : State) (active : Nat) (hsmall : active ≤ 16)
    (hactive : template.activeWords = UInt256.ofNat active)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024) :
    runInstructions zeroProgram (framed template (UInt256.ofNat 2999) rest) =
    some (returned template (UInt256.ofNat 3006) (UInt256.ofNat 0) active rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hp : runInstructions [.op .JUMPDEST, .push 0 0]
      (framed template (UInt256.ofNat 2999) rest) =
      some (framed template (UInt256.ofNat 3001) (UInt256.ofNat 0 :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap0, hz,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have hr := run_return template (UInt256.ofNat 3001) (UInt256.ofNat 0) active hsmall hactive rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hp hr
  have hpc : advancePC 5 (UInt256.ofNat 3001) = UInt256.ofNat 3006 := by decide
  simpa only [zeroProgram, hpc] using both

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn

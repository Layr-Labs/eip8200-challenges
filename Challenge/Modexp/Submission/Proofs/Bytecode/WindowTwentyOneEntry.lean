import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

theorem isTrue_isZero (value : UInt256) :
    UInt256.isTrue (UInt256.isZero value) ↔ value.toNat = 0 := by
  unfold UInt256.isTrue
  rw [Challenge.EvmProof.Word.word_toNat_isZero]
  by_cases h : value.toNat = 0 <;> simp [h]

def testProgram (target : UInt256) : List Instr :=
  [.op .ISZERO, .push 2 target, .op .JUMPI]

theorem run_test (template : State) (pc target value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (testProgram target) (framed template pc (value :: rest)) =
    some (framed template (if value.toNat = 0 then target else advancePC 5 pc) rest) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hpush : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  by_cases hv : value.toNat = 0 <;>
    simp [runInstructions, testProgram, framed, Challenge.EvmProof.Stepper.runInstr,
      hcap1, hcap2, htarget, isTrue_isZero, hv, advancePC, succ_eq_add,
      hpush, word_add_assoc]

def widthDiff (baseSize exponentSize modulusSize : UInt256) : UInt256 :=
  UInt256.lor (UInt256.xor modulusSize (UInt256.ofNat 32))
    (UInt256.lor (UInt256.xor exponentSize (UInt256.ofNat 32))
      (UInt256.gt baseSize (UInt256.ofNat 32)))

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  rw [Fin.xor_val, Fin.xor_val, Nat.xor_comm]

def widthValueProgram : List Instr :=
  [.op .JUMPDEST, .push 1 32, .op (.Dup ⟨1, by decide⟩), .op .GT,
   .op (.Dup ⟨2, by decide⟩), .push 1 32, .op .XOR, .op .OR,
   .op (.Dup ⟨3, by decide⟩), .push 1 32, .op .XOR, .op .OR]

theorem run_width_value (template : State) (baseSize exponentSize modulusSize : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 997) :
    runInstructions widthValueProgram
      (framed template (UInt256.ofNat 2175) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template (UInt256.ofNat 2190)
      (widthDiff baseSize exponentSize modulusSize :: [baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hcap4 : tail.length + 4 < 1024 := by omega
  have hcap5 : tail.length + 5 < 1024 := by omega
  have hcap6 : tail.length + 6 < 1024 := by omega
  simp [runInstructions, widthValueProgram, framed, widthDiff,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5, hcap6, Nat.add_assoc, xor_comm,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

def widthProgram : List Instr := widthValueProgram ++ testProgram (UInt256.ofNat 4787)

theorem run_width (template : State) (baseSize exponentSize modulusSize : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 997)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 4787 = true) :
    runInstructions widthProgram
      (framed template (UInt256.ofNat 2175) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template
      (if (widthDiff baseSize exponentSize modulusSize).toNat = 0
        then UInt256.ofNat 4787 else UInt256.ofNat 2195)
      ([baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hv := run_width_value template baseSize exponentSize modulusSize tail htail
  have ht := run_test template (UInt256.ofNat 2190) (UInt256.ofNat 4787)
    (widthDiff baseSize exponentSize modulusSize) ([baseSize, exponentSize, modulusSize] ++ tail)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 2190) = UInt256.ofNat 2195 := by decide
  simpa only [widthProgram, framed, hpc] using both

def missProgram : List Instr := [.push 2 471, .op .JUMP]

theorem run_miss (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 471 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 2195) rest) =
    some (framed template (UInt256.ofNat 471) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runInstructions, missProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, htarget]

/-- Entry of the one-word core at pc 2240 (0x8c0). Both special-modulus misses
jump here with the loaded modulus word on top of the route frame and `POP`
discards it. There is no base-width branch: a zero-width base runs the core
with the base word `CALLDATALOAD 96 >> 256 = 0`. -/
def baseProgram : List Instr :=
  [.op .JUMPDEST, .op .JUMPDEST]

theorem run_base (template : State) (value : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions baseProgram (framed template (UInt256.ofNat 2199) (value :: rest)) =
    some (framed template (UInt256.ofNat 2201) (value :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runInstructions, baseProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap1, Challenge.EvmProof.Word.succ_ofNat_mod]

def modulusProgram : List Instr :=
  [.op .JUMPDEST, .op .JUMPDEST, .op (.Dup ⟨0, by decide⟩)] ++
    testProgram (UInt256.ofNat 2825)

theorem run_modulus (template : State)
    (value : UInt256) (rest : List UInt256) (hrest : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 2825 = true) :
    runInstructions modulusProgram (framed template (UInt256.ofNat 2201) (value :: rest)) =
    some (framed template (if value.toNat = 0 then UInt256.ofNat 2825 else UInt256.ofNat 2209)
      (value :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hh : runInstructions [.op .JUMPDEST, .op .JUMPDEST, .op (.Dup ⟨0, by decide⟩)]
      (framed template (UInt256.ofNat 2201) (value :: rest)) =
      some (framed template (UInt256.ofNat 2204) (value :: value :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap1,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have ht := run_test template (UInt256.ofNat 2204) (UInt256.ofNat 2825) value
    (value :: rest) (by simp only [List.length_cons]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hh ht
  have hpc : advancePC 5 (UInt256.ofNat 2204) = UInt256.ofNat 2209 := by decide
  simpa only [modulusProgram, framed, hpc] using both

def normalizeProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD, .op (.Dup ⟨2, by decide⟩),
   .push 1 32, .op .SUB, .push 1 3, .op .SHL, .op .SHR]

theorem run_normalize (template : State) (modulus baseOffset : UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoffset : rest[3]? = some baseOffset) :
    runInstructions normalizeProgram
      (framed template (UInt256.ofNat 2209) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 2219)
      (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata baseOffset.toNat)
        (UInt256.ofNat ((32 - baseSize) * 8)) :: modulus :: rest)) := by
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hwidth (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat baseSize) (UInt256.ofNat 3) =
      UInt256.ofNat ((32 - baseSize) * 8) := by
    rw [hsub, Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    congr 1
  simp [runInstructions, normalizeProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap1, hcap2, hcap3, hcap4, List.getElem?_cons_succ, hbase, hoffset,
    Challenge.EvmProof.Word.literal_eq_ofNat, hshift,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry

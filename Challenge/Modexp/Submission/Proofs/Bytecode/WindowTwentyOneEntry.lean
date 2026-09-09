import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput

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
      (framed template (UInt256.ofNat 2613) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template (UInt256.ofNat 2628)
      (widthDiff baseSize exponentSize modulusSize :: [baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hcap3 : tail.length + 3 < 1024 := by omega
  have hcap4 : tail.length + 4 < 1024 := by omega
  have hcap5 : tail.length + 5 < 1024 := by omega
  have hcap6 : tail.length + 6 < 1024 := by omega
  simp [runInstructions, widthValueProgram, framed, widthDiff,
    Challenge.EvmProof.Stepper.runInstr, hcap3, hcap4, hcap5, hcap6, Nat.add_assoc, xor_comm,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

def widthProgram : List Instr := widthValueProgram ++ testProgram (UInt256.ofNat 5233)

theorem run_width (template : State) (baseSize exponentSize modulusSize : UInt256)
    (tail : List UInt256) (htail : tail.length ≤ 997)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 5233 = true) :
    runInstructions widthProgram
      (framed template (UInt256.ofNat 2613) ([baseSize, exponentSize, modulusSize] ++ tail)) =
    some (framed template
      (if (widthDiff baseSize exponentSize modulusSize).toNat = 0
        then UInt256.ofNat 5233 else UInt256.ofNat 2633)
      ([baseSize, exponentSize, modulusSize] ++ tail)) := by
  have hv := run_width_value template baseSize exponentSize modulusSize tail htail
  have ht := run_test template (UInt256.ofNat 2628) (UInt256.ofNat 5233)
    (widthDiff baseSize exponentSize modulusSize) ([baseSize, exponentSize, modulusSize] ++ tail)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 2628) = UInt256.ofNat 2633 := by decide
  simpa only [widthProgram, framed, hpc] using both

def missProgram : List Instr := [.push 2 5323, .op .JUMP]

/-! The word-route miss now enters a narrow exact-vector guard.  The guard
keeps the legacy calling-convention stack intact on both outcomes. -/
def exactCheckProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩), .push 1 1, .op .XOR,
   .op (.Dup ⟨2, by decide⟩), .push 1 1, .op .XOR, .op .OR,
   .op (.Dup ⟨3, by decide⟩), .push 1 1, .op .XOR, .op .OR,
   .op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD, .push 0 0, .op .BYTE,
   .push 1 2, .op .XOR, .op .OR,
   .op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .push 0 0, .op .BYTE,
   .push 1 5, .op .XOR, .op .OR,
   .op (.Dup ⟨6, by decide⟩), .op .CALLDATALOAD, .push 0 0, .op .BYTE,
   .push 1 13, .op .XOR, .op .OR,
   .op .ISZERO, .push 2 5371, .op .JUMPI]

def exactFallbackProgram : List Instr := [.push 2 517, .op .JUMP]

def exactReturnProgram : List Instr :=
  [.op .JUMPDEST, .push 1 6, .push 0 0, .op .MSTORE8,
   .push 1 1, .push 0 0, .op .RETURN]
def exactStack (baseSize exponentSize modulusSize expOffset modOffset : UInt256)
    (tail : List UInt256) : List UInt256 :=
  [baseSize, exponentSize, modulusSize, UInt256.ofNat 96, expOffset, modOffset,
   UInt256.ofNat 1267, modOffset, expOffset, modulusSize, exponentSize, baseSize] ++ tail

abbrev exactDiff := WindowTwentyOneInput.exactDiffOf

def exactStoredMemory (template : State) : ByteArray :=
  MachineState.writeBytes template.memory (ByteArray.mk #[UInt8.ofNat 6]) 0

def exactReturned (template : State) (stack : List UInt256) : State :=
  { template with
    pc := UInt256.ofNat 5380
    stack := stack
    memory := exactStoredMemory template
    activeWords := template.activeWordsAfterUInt256 0 1
    halt := .Returned
    hReturn := MachineState.readPadded (exactStoredMemory template) 0 1 }

theorem run_exactCheck_hit (template : State)
    (baseSize exponentSize modulusSize expOffset modOffset : UInt256)
    (baseByte exponentByte modulusByte : UInt256) (tail : List UInt256)
    (hbase : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata 96) = baseByte)
    (hexponent : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata expOffset.toNat) = exponentByte)
    (hmodulus : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata modOffset.toNat) = modulusByte)
    (hzero : exactDiff baseSize exponentSize modulusSize baseByte exponentByte modulusByte = 0)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 5371 = true) :
    runInstructions exactCheckProgram
      (framed template (UInt256.ofNat 5323)
        (exactStack baseSize exponentSize modulusSize expOffset modOffset tail)) =
    some (framed template (UInt256.ofNat 5371)
      (exactStack baseSize exponentSize modulusSize expOffset modOffset tail)) := by
  have hcap (n : Nat) (hn : n ≤ 13) : tail.length + n < 1024 := by omega
  have hzeroNat :
      (exactDiff baseSize exponentSize modulusSize baseByte exponentByte modulusByte).toNat = 0 := by
    rw [hzero]
    rfl
  simp (disch := omega)
    [runInstructions, exactCheckProgram, exactStack, exactDiff, framed,
      Challenge.EvmProof.Stepper.runInstr, hbase, hexponent, hmodulus, hzeroNat,
      htarget, hcap, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_exactCheck_miss (template : State)
    (baseSize exponentSize modulusSize expOffset modOffset : UInt256)
    (baseByte exponentByte modulusByte : UInt256) (tail : List UInt256)
    (hbase : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata 96) = baseByte)
    (hexponent : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata expOffset.toNat) = exponentByte)
    (hmodulus : UInt256.byteAt ⟨0⟩
      (MachineState.readWord template.executionEnv.calldata modOffset.toNat) = modulusByte)
    (hnonzero :
      exactDiff baseSize exponentSize modulusSize baseByte exponentByte modulusByte ≠ 0) :
    runInstructions exactCheckProgram
      (framed template (UInt256.ofNat 5323)
        (exactStack baseSize exponentSize modulusSize expOffset modOffset tail)) =
    some (framed template (UInt256.ofNat 5367)
      (exactStack baseSize exponentSize modulusSize expOffset modOffset tail)) := by
  have hcap (n : Nat) (hn : n ≤ 13) : tail.length + n < 1024 := by omega
  have hnonzeroNat :
      (exactDiff baseSize exponentSize modulusSize baseByte exponentByte modulusByte).toNat ≠ 0 := by
    intro hz
    apply hnonzero
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp (disch := omega)
    [runInstructions, exactCheckProgram, exactStack, exactDiff, framed,
      Challenge.EvmProof.Stepper.runInstr, hbase, hexponent, hmodulus, hnonzeroNat,
      hcap, UInt256.isZero, Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_exactFallback (template : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 517 = true) :
    runInstructions exactFallbackProgram
      (framed template (UInt256.ofNat 5367) stack) =
    some (framed template (UInt256.ofNat 517) stack) := by
  have hcap : stack.length + 1 < 1024 := by omega
  simp [runInstructions, exactFallbackProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, hstack, hcap, htarget,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_exactReturn (template : State) (stack : List UInt256)
    (hstack : stack.length ≤ 1000) :
    runInstructions exactReturnProgram
      (framed template (UInt256.ofNat 5371) stack) =
    some (exactReturned template stack) := by
  have hcap : stack.length + 2 < 1024 := by omega
  simp (disch := omega)
    [runInstructions, exactReturnProgram, exactReturned, exactStoredMemory, framed,
      Challenge.EvmProof.Stepper.runInstr, hstack, hcap,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_miss (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 5323 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 2633) rest) =
    some (framed template (UInt256.ofNat 5323) rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  simp [runInstructions, missProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, htarget]

def baseProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩)] ++ testProgram (UInt256.ofNat 3276)

theorem run_base (template : State) (baseSize : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hbase : rest[0]? = some baseSize)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 3276 = true) :
    runInstructions baseProgram (framed template (UInt256.ofNat 2637) rest) =
    some (framed template (if baseSize.toNat = 0 then UInt256.ofNat 3276 else UInt256.ofNat 2644) rest) := by
  have hcap : rest.length < 1024 := by omega
  have hh : runInstructions [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩)]
      (framed template (UInt256.ofNat 2637) rest) =
      some (framed template (UInt256.ofNat 2639) (baseSize :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap,
      hbase, Challenge.EvmProof.Word.succ_ofNat_mod]
  have ht := run_test template (UInt256.ofNat 2639) (UInt256.ofNat 3276) baseSize rest hrest htarget
  have both := runInstructions_append_some _ _ _ _ _ hh ht
  have hpc : advancePC 5 (UInt256.ofNat 2639) = UInt256.ofNat 2644 := by decide
  simpa only [baseProgram, framed, hpc] using both

def modulusProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .op (.Dup ⟨0, by decide⟩)] ++
    testProgram (UInt256.ofNat 3268)

theorem run_modulus (template : State) (modulusOffset : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 999)
    (hoffset : rest[5]? = some modulusOffset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 3268 = true) :
    let modulus := MachineState.readWord template.executionEnv.calldata modulusOffset.toNat
    runInstructions modulusProgram (framed template (UInt256.ofNat 2644) rest) =
    some (framed template (if modulus.toNat = 0 then UInt256.ofNat 3268 else UInt256.ofNat 2652)
      (modulus :: rest)) := by
  let modulus := MachineState.readWord template.executionEnv.calldata modulusOffset.toNat
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hh : runInstructions [.op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .op (.Dup ⟨0, by decide⟩)]
      (framed template (UInt256.ofNat 2644) rest) =
      some (framed template (UInt256.ofNat 2647) (modulus :: modulus :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hcap0, hcap1,
      hoffset, modulus, Challenge.EvmProof.Word.succ_ofNat_mod]
  have ht := run_test template (UInt256.ofNat 2647) (UInt256.ofNat 3268) modulus
    (modulus :: rest) (by simp only [List.length_cons]; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hh ht
  have hpc : advancePC 5 (UInt256.ofNat 2647) = UInt256.ofNat 2652 := by decide
  simpa only [modulusProgram, framed, hpc, modulus] using both

def normalizeProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD, .op (.Dup ⟨2, by decide⟩),
   .push 1 32, .op .SUB, .push 1 3, .op .SHL, .op .SHR]

theorem run_normalize (template : State) (modulus baseOffset : UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoffset : rest[3]? = some baseOffset) :
    runInstructions normalizeProgram
      (framed template (UInt256.ofNat 2652) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 2662)
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

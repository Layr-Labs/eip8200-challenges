import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel

def bn : UInt256 := UInt256.ofNat
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

def secp : UInt256 := UInt256.ofNat
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

def primeValue (modulus : UInt256) : UInt256 :=
  UInt256.lor (UInt256.eq secp modulus) (UInt256.eq bn modulus)

private theorem toNat_zero_iff (value : UInt256) : value.toNat = 0 ↔ value = 0 := by
  constructor
  · intro h
    exact Challenge.EvmProof.Word.word_ext h
  · rintro rfl
    rfl

theorem eq_zero_iff (a b : UInt256) : UInt256.eq a b = 0 ↔ a ≠ b := by
  have hi : a.toNat = b.toNat ↔ a = b :=
    ⟨Challenge.EvmProof.Word.word_ext, congrArg UInt256.toNat⟩
  have hz : UInt256.ofNat 0 = 0 := rfl
  have ho : UInt256.ofNat 1 ≠ 0 := by decide
  simp [UInt256.eq, hi, hz, ho]

theorem primeValue_nonzero (modulus : UInt256) :
    (primeValue modulus).toNat ≠ 0 ↔ modulus = bn ∨ modulus = secp := by
  rw [ne_eq, toNat_zero_iff, primeValue, WindowGuardLogic.wordOr_eq_zero_iff,
    eq_zero_iff, eq_zero_iff]
  tauto

def primeValueProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD,
   .op (.Dup ⟨0, by decide⟩), .push 32 bn, .op .EQ,
   .op (.Dup ⟨1, by decide⟩), .push 5 0x01000003d0, .op .NOT, .op .EQ, .op .OR]

def primeProgram : List Instr := primeValueProgram ++ WindowTwentyOneEntry.testProgram (UInt256.ofNat 5319)

def exponentValueProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .push 1 1,
   .op (.Dup ⟨2, by decide⟩), .op .SUB, .op .EQ]

def exponentProgram : List Instr := exponentValueProgram ++
  WindowTwentyOneEntry.testProgram (UInt256.ofNat 5319)

def valueProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD] ++
    WindowTwentyOneEntry.normalizeProgram.drop 2 ++
    [.op .MOD, .op .ISZERO, .op .ISZERO]

def returnProgram : List Instr := valueProgram ++ WindowTwentyOneReturn.program

def missProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .push 2 2637, .op .JUMP]

theorem run_prime (template : State) (offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[5]? = some offset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 5319 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 5235) rest) =
    some (framed template
      (if (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0
        then UInt256.ofNat 5319 else UInt256.ofNat 5288)
      (MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = secp := by decide
  have hv : runInstructions primeValueProgram (framed template (UInt256.ofNat 5235) rest) =
      some (framed template (UInt256.ofNat 5283)
        (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat) ::
          MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)) := by
    simp (config := { maxSteps := 500000 }) [primeValueProgram, primeValue, runInstructions, framed, hoff,
      Challenge.EvmProof.Stepper.runInstr, hc0, hc1, hc2, hc3, hc4, hsecp,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 5283) (UInt256.ofNat 5319)
    (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat))
    (MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 5283) = UInt256.ofNat 5288 := by decide
  simpa only [primeProgram, hpc, framed] using both

theorem run_exponent (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[4]? = some offset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 5319 = true) :
    runInstructions exponentProgram (framed template (UInt256.ofNat 5288) (modulus :: rest)) =
    some (framed template
      (if (UInt256.eq (modulus - UInt256.ofNat 1)
        (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0
        then UInt256.ofNat 5319 else UInt256.ofNat 5300)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hv : runInstructions exponentValueProgram (framed template (UInt256.ofNat 5288)
      (modulus :: rest)) =
      some (framed template (UInt256.ofNat 5295)
        (UInt256.eq (modulus - UInt256.ofNat 1)
          (MachineState.readWord template.executionEnv.calldata offset.toNat) :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 }) [exponentValueProgram, runInstructions, framed, hoff,
      Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 5295) (UInt256.ofNat 5319)
    (UInt256.eq (modulus - UInt256.ofNat 1)
      (MachineState.readWord template.executionEnv.calldata offset.toNat)) (modulus :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 5295) = UInt256.ofNat 5300 := by decide
  simpa only [exponentProgram, hpc, framed] using both

private theorem run_value (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoff : rest[3]? = some offset) :
    runInstructions valueProgram (framed template (UInt256.ofNat 5300) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 5313)
      (UInt256.isZero (UInt256.isZero (UInt256.mod
        (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata offset.toNat)
          (UInt256.ofNat ((32 - baseSize) * 8))) modulus)) :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hwidth (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat baseSize)
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - baseSize) * 8) := by
    rw [hsub, Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    congr 1
  simp (config := { maxSteps := 500000 }) [valueProgram, WindowTwentyOneEntry.normalizeProgram,
    runInstructions, framed, hbase, hoff, hshift,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_return (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoff : rest[3]? = some offset) (active : Nat) (hsmall : active ≤ 16)
    (hactive : template.activeWords = UInt256.ofNat active) :
    runInstructions returnProgram (framed template (UInt256.ofNat 5300) (modulus :: rest)) =
    some (WindowTwentyOneReturn.returned template (UInt256.ofNat 5318)
      (UInt256.isZero (UInt256.isZero (UInt256.mod
        (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata offset.toNat)
          (UInt256.ofNat ((32 - baseSize) * 8))) modulus))) active rest) := by
  let word := UInt256.isZero (UInt256.isZero (UInt256.mod
    (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata offset.toNat)
      (UInt256.ofNat ((32 - baseSize) * 8))) modulus))
  have hv := run_value template modulus offset rest baseSize hwidth hrest hbase hoff
  have hr := WindowTwentyOneReturn.run_return template (UInt256.ofNat 5313) word active
    hsmall hactive rest (by omega)
  have both := runInstructions_append_some _ _ _ _ _ hv hr
  have hpc : advancePC 5 (UInt256.ofNat 5313) = UInt256.ofNat 5318 := by decide
  simpa only [returnProgram, hpc, word] using both

theorem run_miss (template : State) (value : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2637 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 5319) (value :: rest)) =
    some (framed template (UInt256.ofNat 2637) rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  simp [missProgram, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
    hc0, hc1, hjump, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  prime : WindowTwentyOneBinding.Block artifact fork 5235 primeProgram
  exponent : WindowTwentyOneBinding.Block artifact fork 5288 exponentProgram
  result : WindowTwentyOneBinding.Block artifact fork 5300 returnProgram
  miss : WindowTwentyOneBinding.Block artifact fork 5319 missProgram
  missJump : Decode.isValidJumpDest artifact.code 5319 = true
  legacyJump : Decode.isValidJumpDest artifact.code 2637 = true

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

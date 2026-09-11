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

/-- Both special-modulus tests jump straight to the one-word core entry 2240
(0x8c0) when they miss. -/
def primeProgram : List Instr := primeValueProgram ++ WindowTwentyOneEntry.testProgram (UInt256.ofNat 2240)

def exponentValueProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .push 1 1,
   .op (.Dup ⟨2, by decide⟩), .op .SUB, .op .EQ]

def exponentProgram : List Instr := exponentValueProgram ++
  WindowTwentyOneEntry.testProgram (UInt256.ofNat 2240)

private theorem zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt ({ val := 0 } : UInt256) x = UInt256.isZero (UInt256.isZero x) := by
  unfold UInt256.lt UInt256.isZero
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : x.toNat = 0
  · simp [h, hzero]
  · have hp : 0 < x.toNat := Nat.pos_of_ne_zero h
    simp [h, hzero, Nat.not_le_of_gt hp]

def valueProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op .CALLDATALOAD] ++
    WindowTwentyOneEntry.normalizeProgram.drop 2 ++
    [.op .MOD, .push 0 0, .op .LT]

def returnProgram : List Instr := valueProgram ++ WindowTwentyOneReturn.program

theorem run_prime (template : State) (offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[5]? = some offset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 2240 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 4767) rest) =
    some (framed template
      (if (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0
        then UInt256.ofNat 2240 else UInt256.ofNat 4820)
      (MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = secp := by decide
  have hv : runInstructions primeValueProgram (framed template (UInt256.ofNat 4767) rest) =
      some (framed template (UInt256.ofNat 4815)
        (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat) ::
          MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)) := by
    simp (config := { maxSteps := 500000 }) [primeValueProgram, primeValue, runInstructions, framed, hoff,
      Challenge.EvmProof.Stepper.runInstr, hc0, hc1, hc2, hc3, hc4, hsecp,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 4815) (UInt256.ofNat 2240)
    (primeValue (MachineState.readWord template.executionEnv.calldata offset.toNat))
    (MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 4815) = UInt256.ofNat 4820 := by decide
  simpa only [primeProgram, hpc, framed] using both

theorem run_exponent (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[4]? = some offset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 2240 = true) :
    runInstructions exponentProgram (framed template (UInt256.ofNat 4820) (modulus :: rest)) =
    some (framed template
      (if (UInt256.eq (modulus - UInt256.ofNat 1)
        (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0
        then UInt256.ofNat 2240 else UInt256.ofNat 4832)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hv : runInstructions exponentValueProgram (framed template (UInt256.ofNat 4820)
      (modulus :: rest)) =
      some (framed template (UInt256.ofNat 4827)
        (UInt256.eq (modulus - UInt256.ofNat 1)
          (MachineState.readWord template.executionEnv.calldata offset.toNat) :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 }) [exponentValueProgram, runInstructions, framed, hoff,
      Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 4827) (UInt256.ofNat 2240)
    (UInt256.eq (modulus - UInt256.ofNat 1)
      (MachineState.readWord template.executionEnv.calldata offset.toNat)) (modulus :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 4827) = UInt256.ofNat 4832 := by decide
  simpa only [exponentProgram, hpc, framed] using both

private theorem run_value (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoff : rest[3]? = some offset) :
    runInstructions valueProgram (framed template (UInt256.ofNat 4832) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 4845)
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
    Challenge.EvmProof.Word.literal_eq_ofNat, zero_lt_eq_double_isZero,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_return (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[0]? = some (UInt256.ofNat baseSize))
    (hoff : rest[3]? = some offset) (active : Nat) (hsmall : active ≤ 16)
    (hactive : template.activeWords = UInt256.ofNat active) :
    runInstructions returnProgram (framed template (UInt256.ofNat 4832) (modulus :: rest)) =
    some (WindowTwentyOneReturn.returned template (UInt256.ofNat 4850)
      (UInt256.isZero (UInt256.isZero (UInt256.mod
        (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata offset.toNat)
          (UInt256.ofNat ((32 - baseSize) * 8))) modulus))) active rest) := by
  let word := UInt256.isZero (UInt256.isZero (UInt256.mod
    (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata offset.toNat)
      (UInt256.ofNat ((32 - baseSize) * 8))) modulus))
  have hv := run_value template modulus offset rest baseSize hwidth hrest hbase hoff
  have hr := WindowTwentyOneReturn.run_return template (UInt256.ofNat 4845) word active
    hsmall hactive rest (by omega)
  have both := runInstructions_append_some _ _ _ _ _ hv hr
  have hpc : advancePC 5 (UInt256.ofNat 4845) = UInt256.ofNat 4850 := by decide
  simpa only [returnProgram, hpc, word] using both

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  prime : WindowTwentyOneBinding.Block artifact fork 4767 primeProgram
  exponent : WindowTwentyOneBinding.Block artifact fork 4820 exponentProgram
  result : WindowTwentyOneBinding.Block artifact fork 4832 returnProgram
  legacyJump : Decode.isValidJumpDest artifact.code 2240 = true

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

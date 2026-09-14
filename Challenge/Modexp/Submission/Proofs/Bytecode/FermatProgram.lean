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

private theorem zero_lt_eq_double_isZero (x : UInt256) :
    UInt256.lt ({ val := 0 } : UInt256) x = UInt256.isZero (UInt256.isZero x) := by
  unfold UInt256.lt UInt256.isZero
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases h : x.toNat = 0
  · simp [h, hzero]
  · have hp : 0 < x.toNat := Nat.pos_of_ne_zero h
    simp [h, hzero, Nat.not_le_of_gt hp]


/-- Fermat exit at 95: load the base word at calldata 96, normalize it by the
declared base width (depth six under the modulus word), reduce it modulo the
prime and return `0 < base mod p`. -/
def valueProgram : List Instr :=
  [.push 1 96, .op .CALLDATALOAD, .op (.Dup ⟨6, by decide⟩),
   .push 1 32, .op .SUB, .push 1 3, .op .SHL, .op .SHR,
   .op .MOD, .push 0 0, .op .LT]

def returnProgram : List Instr := valueProgram ++ WindowTwentyOneReturn.program

private theorem run_value (template : State) (modulus : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[4]? = some (UInt256.ofNat baseSize)) :
    runInstructions valueProgram (framed template (UInt256.ofNat 96) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 110)
      (UInt256.isZero (UInt256.isZero (UInt256.mod
        (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
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
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  simp (config := { maxSteps := 500000 }) [valueProgram,
    runInstructions, framed, hbase, hshift, h96,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4,
    Challenge.EvmProof.Word.literal_eq_ofNat, zero_lt_eq_double_isZero,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  rfl

theorem run_return (template : State) (modulus : UInt256) (rest : List UInt256)
    (baseSize : Nat) (hwidth : baseSize ≤ 32)
    (hrest : rest.length ≤ 999) (hbase : rest[4]? = some (UInt256.ofNat baseSize))
    (active : Nat) (hsmall : active ≤ 16)
    (hactive : template.activeWords = UInt256.ofNat active) :
    runInstructions returnProgram (framed template (UInt256.ofNat 96) (modulus :: rest)) =
    some (WindowTwentyOneReturn.returned template (UInt256.ofNat 115)
      (UInt256.isZero (UInt256.isZero (UInt256.mod
        (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
          (UInt256.ofNat ((32 - baseSize) * 8))) modulus))) active rest) := by
  let word := UInt256.isZero (UInt256.isZero (UInt256.mod
    (UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
      (UInt256.ofNat ((32 - baseSize) * 8))) modulus))
  have hv := run_value template modulus rest baseSize hwidth hrest hbase
  have hr := WindowTwentyOneReturn.run_return template (UInt256.ofNat 110) word active
    (by omega) hactive rest (by omega)
  have both := runInstructions_append_some _ _ _ _ _ hv hr
  have hpc : advancePC 5 (UInt256.ofNat 110) = UInt256.ofNat 115 := by decide
  simpa only [returnProgram, hpc, word] using both


end Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

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


/-- Fermat exit at 92: copy the (width-normalized) base word kept at depth three under the
modulus word, reduce it modulo the prime and compute `0 < base mod p`. -/
def valueProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op .MOD, .push 0 0, .op .LT]

/-- 98: store the result word at 0 and return `MSIZE` (one word) bytes from 0. -/
def exitProgram : List Instr :=
  [.push 0 0, .op .MSTORE, .op .MSIZE, .push 0 0, .op .RETURN]

def returnProgram : List Instr := valueProgram ++ exitProgram

private theorem run_value (template : State) (modulus base : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hbase : rest[1]? = some base) :
    runInstructions valueProgram (framed template (UInt256.ofNat 92) (modulus :: rest)) =
    some (framed template (UInt256.ofNat 96)
      (UInt256.isZero (UInt256.isZero (UInt256.mod base modulus)) :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 500000 }) [valueProgram,
    runInstructions, framed, hbase,
    Challenge.EvmProof.Stepper.runInstr, hc1, hc2,
    Challenge.EvmProof.Word.literal_eq_ofNat, zero_lt_eq_double_isZero,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  rfl

/-- The exit on untouched memory: `MSIZE` reads exactly one word after the store. -/
theorem run_exit (template : State) (pc word : UInt256)
    (hactive : template.activeWords = UInt256.ofNat 0)
    (rest : List UInt256) (hrest : rest.length + 3 < 1024) :
    WindowTwentyOneMsize.runInstructionsX exitProgram
      (WindowTwentyOneReturn.framed template pc (word :: rest)) =
    some (WindowTwentyOneReturn.returned template (advancePC 4 pc) word 0 rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have ha : (UInt256.ofNat 0).toNat = 0 := rfl
  simp [WindowTwentyOneMsize.runInstructionsX, WindowTwentyOneMsize.runInstrX_msize,
    exitProgram, WindowTwentyOneReturn.framed, WindowTwentyOneReturn.returned,
    Challenge.EvmProof.Stepper.runInstr,
    hcap0, hcap1, hcap2, hzero, hactive, ha, WindowTableMemory.storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    advancePC, succ_eq_add, word_add_assoc]

theorem run_return (template : State) (modulus base : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hbase : rest[1]? = some base)
    (hactive : template.activeWords = UInt256.ofNat 0) :
    WindowTwentyOneMsize.runInstructionsX returnProgram
      (framed template (UInt256.ofNat 92) (modulus :: rest)) =
    some (WindowTwentyOneReturn.returned template (UInt256.ofNat 100)
      (UInt256.isZero (UInt256.isZero (UInt256.mod base modulus))) 0 rest) := by
  let word := UInt256.isZero (UInt256.isZero (UInt256.mod base modulus))
  have hv := run_value template modulus base rest hrest hbase
  have hvx : WindowTwentyOneMsize.runInstructionsX valueProgram
      (framed template (UInt256.ofNat 92) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 96) (word :: rest)) := by
    rw [WindowTwentyOneMsize.runInstructionsX_eq valueProgram (by decide)]
    exact hv
  have hr := run_exit template (UInt256.ofNat 96) word hactive rest (by omega)
  have both := WindowTwentyOneMsize.runInstructionsX_append_some _ _ _ _ _ hvx hr
  have hpc : advancePC 4 (UInt256.ofNat 96) = UInt256.ofNat 100 := by decide
  simpa only [returnProgram, hpc, word] using both


end Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

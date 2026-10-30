import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentProgram

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.FermatNext
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel
open HistoricalSearch

/-- Fast loads at 16 (exponent and modulus sizes 32): the base word (unshifted for a 32-byte
base), then the exponent and modulus words from their fixed offsets 128 and 160. For another
base size these are garbage words that the merged test at 25 never trusts. -/
def fastProgram : List Instr :=
  [.push 1 96, .op .CALLDATALOAD, .push 1 128, .op .CALLDATALOAD, .push 1 160, .op .CALLDATALOAD]

/-- Merged test at 25: `(baseSize = 32) * fermatDiff`. Nonzero means a 32-byte base and
`exponent ≠ modulus - 1`, and goes straight to the window core at 745. -/
def mergeProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .NOT, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .push 0 0, .op .CALLDATALOAD, .push 1 32, .op .EQ, .op .MUL, .push 2 745, .op .JUMPI]

/-- 39: a base size other than 32 goes to the general-width entry at 101. -/
def recheckProgram : List Instr :=
  [.push 0 0, .op .CALLDATALOAD, .push 1 32, .op .XOR, .push 1 101, .op .JUMPI]

/-- Join point at 47 (also the general-width entry's join): jump to the window core at 745
unless `exponent = modulus - 1`, in which case fall through to the jump to the prime test. -/
def joinProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨1, by decide⟩), .op .NOT, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .push 2 745, .op .JUMPI]

/-- 56: the special-prime test lives at the end of the image (10698). -/
def toPrimeProgram : List Instr := [.push 2 10698, .op .JUMP]

/-- General-width entry at 103 (exponent and modulus sizes 32, base size not 32):
a base size above 32 leaves for the wide fallback at 238. -/
def genCheckProgram : List Instr :=
  [.op .JUMPDEST, .push 1 32, .push 0 0, .op .CALLDATALOAD,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .push 1 219, .op .JUMPI]

/-- 112: with `k = 32 - baseSize`, push `k`, the base word shifted right by `8 k`, the exponent
word at `128 - k` and the modulus word at `160 - k`, then join at 47. -/
def genLoadProgram : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op .SUB,
   .push 1 96, .op .CALLDATALOAD, .op (.Dup ⟨1, by decide⟩), .push 1 3, .op .SHL, .op .SHR,
   .op (.Dup ⟨1, by decide⟩), .push 1 128, .op .SUB, .op .CALLDATALOAD,
   .op (.Dup ⟨2, by decide⟩), .push 1 160, .op .SUB, .op .CALLDATALOAD,
   .push 1 47, .op .JUMP]

/-- `modulus + ~exponent`, zero exactly when `exponent = modulus - 1` (mod 2^256). -/
def fermatDiff (modulus exponent : UInt256) : UInt256 :=
  modulus + UInt256.lnot exponent

theorem fermatDiff_zero (modulus exponent : UInt256)
    (h : (fermatDiff modulus exponent).toNat = 0) :
    modulus - UInt256.ofNat 1 = exponent := by
  apply Challenge.EvmProof.Word.word_ext
  rw [fermatDiff, Challenge.EvmProof.Word.word_toNat_add] at h
  have hl : (UInt256.lnot exponent).toNat = 2 ^ 256 - 1 - exponent.toNat := by
    have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - exponent.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl] at h
  rw [Challenge.EvmProof.Word.word_toNat_sub]
  have h1 : (UInt256.ofNat 1).toNat = 1 := by decide
  rw [h1]
  have hm : modulus.toNat < 2 ^ 256 := modulus.val.isLt
  have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
  omega

theorem fermatDiff_one (modulus exponent : UInt256)
    (h : (fermatDiff modulus exponent).toNat = 1) :
    modulus - UInt256.ofNat 2 = exponent := by
  apply Challenge.EvmProof.Word.word_ext
  rw [fermatDiff, Challenge.EvmProof.Word.word_toNat_add] at h
  have hl : (UInt256.lnot exponent).toNat = 2 ^ 256 - 1 - exponent.toNat := by
    have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - exponent.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl] at h
  rw [Challenge.EvmProof.Word.word_toNat_sub]
  have h2 : (UInt256.ofNat 2).toNat = 2 := by decide
  rw [h2]
  have hm : modulus.toNat < 2 ^ 256 := modulus.val.isLt
  have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
  omega

/-- The join guard vanishes exactly when `fermatDiff` does. -/
theorem joinGuard_zero_iff (modulus exponent : UInt256) :
    (UInt256.xor modulus (exponent + UInt256.ofNat 1)).toNat = 0 ↔
      (fermatDiff modulus exponent).toNat = 0 := by
  have hz : ∀ w : UInt256, w.toNat = 0 ↔ w = 0 := by
    intro w
    constructor
    · intro h; exact Challenge.EvmProof.Word.word_ext (by rw [h]; rfl)
    · intro h; rw [h]; rfl
  rw [hz, WindowGuardLogic.wordXor_eq_zero_iff, fermatDiff,
    Challenge.EvmProof.Word.word_toNat_add]
  have hl : (UInt256.lnot exponent).toNat = 2 ^ 256 - 1 - exponent.toNat := by
    have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
    rw [UInt256.lnot, Challenge.EvmProof.Word.word_toNat_ofNat]
    change (2 ^ 256 - 1 - exponent.toNat) % 2 ^ 256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [hl]
  have hm : modulus.toNat < 2 ^ 256 := modulus.val.isLt
  have he : exponent.toNat < 2 ^ 256 := exponent.val.isLt
  constructor
  · intro h
    have h' := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat] at h'
    omega
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    rw [Challenge.EvmProof.Word.word_toNat_add, Challenge.EvmProof.Word.word_toNat_ofNat]
    omega

def jumpTailProgram : List Instr := [.push 2 745, .op .JUMP]
/-- The landing pad at 4847, directly before the result at 4848. The prime test
jumps here; the join guard already established `exponent = modulus - 1`. -/
def tailProgram : List Instr :=
  [.op .JUMPDEST]

def primeValueProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 32 FermatProgram.bn, .op .EQ,
   .op (.Dup ⟨1, by decide⟩), .push 5 0x01000003d0, .op .NOT,
   .op .EQ, .op .OR]

/-- The special-prime test at 10698: BN254 or secp256k1 modulus goes to the Fermat result. -/
def primeProgram : List Instr :=
  [.op .JUMPDEST] ++ primeValueProgram ++ [.push 2 4847, .op .JUMPI]

/-- `(baseSize = 32) * fermatDiff`, the merged test word. -/
def mergeWord (calldata : ByteArray) (modulus exponent : UInt256) : UInt256 :=
  UInt256.eq (UInt256.ofNat 32) (MachineState.readWord calldata 0) * fermatDiff modulus exponent

set_option linter.unusedSimpArgs false in
theorem run_fast (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions fastProgram (framed template (UInt256.ofNat 16) rest) =
    some (framed template (UInt256.ofNat 25)
      (MachineState.readWord template.executionEnv.calldata 160 ::
        MachineState.readWord template.executionEnv.calldata 128 ::
        MachineState.readWord template.executionEnv.calldata 96 :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  have h128 : (UInt256.ofNat 128).toNat = 128 := by decide
  have h160 : (UInt256.ofNat 160).toNat = 160 := by decide
  simp [fastProgram, runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
    hz, h96, h128, h160, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_merge (template : State) (modulus exponent : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions mergeProgram
      (framed template (UInt256.ofNat 25) (modulus :: exponent :: rest)) =
    some (framed template
      (if (mergeWord template.executionEnv.calldata modulus exponent).toNat = 0
        then UInt256.ofNat 39 else UInt256.ofNat 745)
      (modulus :: exponent :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  by_cases hm : (mergeWord template.executionEnv.calldata modulus exponent).toNat = 0
  · have hx : (UInt256.eq (UInt256.ofNat 32) (MachineState.readWord template.executionEnv.calldata 0) *
        (modulus + UInt256.lnot exponent)).toNat = 0 := hm
    simp (config := { maxSteps := 500000 }) [mergeProgram, runInstructions, framed,
      htarget, hm, hx, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  · have hx : ¬ (UInt256.eq (UInt256.ofNat 32) (MachineState.readWord template.executionEnv.calldata 0) *
        (modulus + UInt256.lnot exponent)).toNat = 0 := hm
    simp (config := { maxSteps := 500000 }) [mergeProgram, runInstructions, framed,
      htarget, hm, hx, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_recheck (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 101 = true) :
    runInstructions recheckProgram (framed template (UInt256.ofNat 39) rest) =
    some (framed template
      (if (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord template.executionEnv.calldata 0)).toNat = 0
        then UInt256.ofNat 47 else UInt256.ofNat 101) rest) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  by_cases hv : (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord template.executionEnv.calldata 0)).toNat = 0 <;>
    simp (config := { maxSteps := 500000 }) [recheckProgram, runInstructions, framed,
      htarget, hv, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_join (template : State) (modulus exponent : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions joinProgram
      (framed template (UInt256.ofNat 47) (modulus :: exponent :: rest)) =
    some (framed template
      (if (fermatDiff modulus exponent).toNat = 0 then UInt256.ofNat 56 else UInt256.ofNat 745)
      (modulus :: exponent :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  by_cases hz : (fermatDiff modulus exponent).toNat = 0
  · have hx : (modulus + UInt256.lnot exponent).toNat = 0 := hz
    simp (config := { maxSteps := 500000 }) [joinProgram, runInstructions, framed,
      htarget, hz, hx, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  · have hx : ¬ (modulus + UInt256.lnot exponent).toNat = 0 := hz
    simp (config := { maxSteps := 500000 }) [joinProgram, runInstructions, framed,
      htarget, hz, hx, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_toPrime (template : State) (rest : List UInt256) (hrest : rest.length < 1023)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 10698 = true) :
    runInstructions toPrimeProgram (framed template (UInt256.ofNat 56) rest) =
    some (framed template (UInt256.ofNat 10698) rest) := by
  have hc : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  simp [toPrimeProgram,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,hc,hc1,
    htarget,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_gen_check (template : State) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 219 = true) :
    runInstructions genCheckProgram (framed template (UInt256.ofNat 101) rest) =
    some (framed template
      (if (UInt256.gt (MachineState.readWord template.executionEnv.calldata 0)
          (UInt256.ofNat 32)).toNat = 0 then UInt256.ofNat 112 else UInt256.ofNat 219)
      (MachineState.readWord template.executionEnv.calldata 0 :: UInt256.ofNat 32 :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0 : (UInt256.ofNat 0).toNat = 0 := by decide
  by_cases hv : (UInt256.gt (MachineState.readWord template.executionEnv.calldata 0)
      (UInt256.ofNat 32)).toNat = 0 <;>
    simp (config := { maxSteps := 500000 }) [genCheckProgram, runInstructions, framed,
      htarget, hv, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
      hz, h0,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_gen_load (template : State) (b : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 47 = true) :
    runInstructions genLoadProgram
      (framed template (UInt256.ofNat 112) (b :: UInt256.ofNat 32 :: rest)) =
    some (framed template (UInt256.ofNat 47)
      (MachineState.readWord template.executionEnv.calldata
          (UInt256.ofNat 160 - (UInt256.ofNat 32 - b)).toNat ::
        MachineState.readWord template.executionEnv.calldata
          (UInt256.ofNat 128 - (UInt256.ofNat 32 - b)).toNat ::
        UInt256.shiftRight (MachineState.readWord template.executionEnv.calldata 96)
          (UInt256.shiftLeft (UInt256.ofNat 32 - b) (UInt256.ofNat 3)) ::
        (UInt256.ofNat 32 - b) :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  have hk4 : rest.length + 4 < 1024 := by omega
  have hk5 : rest.length + 5 < 1024 := by omega
  have hk6 : rest.length + 6 < 1024 := by omega
  have hk7 : rest.length + 7 < 1024 := by omega
  have h96 : (UInt256.ofNat 96).toNat = 96 := by decide
  simp (config := { maxSteps := 500000 }) [genLoadProgram, runInstructions, framed,
    htarget, List.exchange, h96, Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prime (template : State) (modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 4847 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 10698) (modulus :: rest)) =
    some (framed template
      (if (FermatProgram.primeValue modulus).toNat = 0
        then UInt256.ofNat 10748 else UInt256.ofNat 4847)
      (modulus :: rest)) := by
  have hc0 : rest.length + 1 < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = FermatProgram.secp := by decide
  have hd : runInstructions [.op .JUMPDEST]
      (framed template (UInt256.ofNat 10698) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 10699) (modulus :: rest)) := by
    simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr, hc0,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have hv : runInstructions primeValueProgram
      (framed template (UInt256.ofNat 10699) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 10744)
        (FermatProgram.primeValue modulus :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 })
      [primeValueProgram, FermatProgram.primeValue, runInstructions, framed,
        Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hsecp,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have ht : runInstructions [.push 2 4847, .op .JUMPI]
      (framed template (UInt256.ofNat 10744)
        (FermatProgram.primeValue modulus :: modulus :: rest)) =
      some (framed template
        (if (FermatProgram.primeValue modulus).toNat = 0
          then UInt256.ofNat 10748 else UInt256.ofNat 4847)
        (modulus :: rest)) := by
    by_cases hp : (FermatProgram.primeValue modulus).toNat = 0 <;>
      simp [runInstructions, framed, Challenge.EvmProof.Stepper.runInstr,
        hc1, hc2, htarget, UInt256.isTrue, hp,
        Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod] <;>
      omega
  exact runInstructions_append_some _ _ _ _ _ (runInstructions_append_some _ _ _ _ _ hd hv) ht

theorem run_jumpTail (template : State) (rest : List UInt256) (hrest : rest.length < 1023)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 745 = true) :
    runInstructions jumpTailProgram (framed template (UInt256.ofNat 10748) rest) =
    some (framed template (UInt256.ofNat 745) rest) := by
  have hc : rest.length < 1024 := by omega
  have hc1 : rest.length+1 < 1024 := by omega
  simp [jumpTailProgram,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,hc,hc1,
    htarget,Challenge.EvmProof.Word.literal_eq_ofNat,Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail (template : State) (modulus exponent : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions tailProgram
      (framed template (UInt256.ofNat 4847) (modulus :: exponent :: rest)) =
    some (framed template (UInt256.ofNat 4848) (modulus :: exponent :: rest)) := by
  have hk0 : rest.length < 1024 := by omega
  have hk1 : rest.length + 1 < 1024 := by omega
  have hk2 : rest.length + 2 < 1024 := by omega
  have hk3 : rest.length + 3 < 1024 := by omega
  simp (config := { maxSteps := 500000 }) [tailProgram, runInstructions, framed,
    Challenge.EvmProof.Stepper.runInstr, hk0, hk1, hk2, hk3,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  fast : WindowTwentyOneBinding.Block artifact fork 16 fastProgram
  merge : WindowTwentyOneBinding.Block artifact fork 25 mergeProgram
  recheck : WindowTwentyOneBinding.Block artifact fork 39 recheckProgram
  join : WindowTwentyOneBinding.Block artifact fork 47 joinProgram
  toPrime : WindowTwentyOneBinding.Block artifact fork 56 toPrimeProgram
  prime : WindowTwentyOneBinding.Block artifact fork 10698 primeProgram
  jumpTail : WindowTwentyOneBinding.Block artifact fork 10748 jumpTailProgram
  tail : WindowTwentyOneBinding.Block artifact fork 4847 tailProgram
  result : WindowTwentyOneBinding.Block artifact fork 4848 FermatProgram.returnProgram
  genCheck : WindowTwentyOneBinding.Block artifact fork 101 genCheckProgram
  genLoad : WindowTwentyOneBinding.Block artifact fork 112 genLoadProgram
  routeJump : Decode.isValidJumpDest artifact.code 745 = true
  joinJump : Decode.isValidJumpDest artifact.code 47 = true
  bigJump : Decode.isValidJumpDest artifact.code 219 = true
  tailJump : Decode.isValidJumpDest artifact.code 4847 = true
  primeJump : Decode.isValidJumpDest artifact.code 10698 = true
  genJump : Decode.isValidJumpDest artifact.code 101 = true

end CycleSubmission.Global.FermatNext

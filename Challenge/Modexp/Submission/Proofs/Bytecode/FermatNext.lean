import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel

/-- The early one-word entry at 25.  From the three header sizes it loads the
exponent and modulus words, keeps the exponent offset, and jumps straight to the
window core at 1780 unless `exponent = modulus - 1`, in which case it falls
through to the special-prime test at 45. -/
def entryProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨2, by decide⟩), .push 1 96, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op .CALLDATALOAD,
   .push 1 32, .op (.Dup ⟨2, by decide⟩), .op .ADD, .op .CALLDATALOAD,
   .op (.Dup ⟨1, by decide⟩), .op .NOT, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .push 2 866, .op .JUMPI]

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

def primeValueProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 32 FermatProgram.bn, .op .EQ,
   .op (.Dup ⟨1, by decide⟩), .push 6 0x01000003d0, .op .NOT,
   .op .EQ, .op .OR]

def primeProgram : List Instr :=
  primeValueProgram ++ WindowTwentyOneEntry.testProgram (UInt256.ofNat 866)

theorem run_entry (template : State) (b e m : UInt256)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 866 = true) :
    runInstructions entryProgram (framed template (UInt256.ofNat 25) [m, e, b]) =
    some (framed template
      (if (fermatDiff
          (MachineState.readWord template.executionEnv.calldata
            ((UInt256.ofNat 96 + b) + UInt256.ofNat 32).toNat)
          (MachineState.readWord template.executionEnv.calldata (UInt256.ofNat 96 + b).toNat)).toNat = 0
        then UInt256.ofNat 45 else UInt256.ofNat 866)
      [MachineState.readWord template.executionEnv.calldata
          ((UInt256.ofNat 96 + b) + UInt256.ofNat 32).toNat,
        MachineState.readWord template.executionEnv.calldata (UInt256.ofNat 96 + b).toNat,
        UInt256.ofNat 96 + b, m, e, b]) := by
  simp only [fermatDiff]
  by_cases hz : (MachineState.readWord template.executionEnv.calldata
        ((UInt256.ofNat 96 + b) + UInt256.ofNat 32).toNat +
      UInt256.lnot (MachineState.readWord template.executionEnv.calldata
        (UInt256.ofNat 96 + b).toNat)).toNat = 0 <;>
    simp (config := { maxSteps := 500000 }) [entryProgram, runInstructions, framed,
      htarget, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prime (template : State) (modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 866 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 45) (modulus :: rest)) =
    some (framed template
      (if (FermatProgram.primeValue modulus).toNat = 0
        then UInt256.ofNat 866 else UInt256.ofNat 96)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = FermatProgram.secp := by decide
  have hv : runInstructions primeValueProgram
      (framed template (UInt256.ofNat 45) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 91)
        (FermatProgram.primeValue modulus :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 })
      [primeValueProgram, FermatProgram.primeValue, runInstructions, framed,
        Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hsecp,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 91)
    (UInt256.ofNat 866) (FermatProgram.primeValue modulus) (modulus :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 91) = UInt256.ofNat 96 := by decide
  simpa only [primeProgram, hpc, framed] using both

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  entry : WindowTwentyOneBinding.Block artifact fork 25 entryProgram
  prime : WindowTwentyOneBinding.Block artifact fork 45 primeProgram
  result : WindowTwentyOneBinding.Block artifact fork 96 FermatProgram.returnProgram
  legacyJump : Decode.isValidJumpDest artifact.code 866 = true

#print axioms run_prime
end Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

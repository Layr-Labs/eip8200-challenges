import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowTwentyOneEntry WindowNibbleKernel

def loadProgram : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD]

def exponentProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op .CALLDATALOAD, .push 1 1,
   .op (.Dup ⟨2, by decide⟩), .op .SUB, .op .XOR,
   .push 2 1773, .op .JUMPI]

def primeValueProgram : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 32 FermatProgram.bn, .op .EQ,
   .op (.Dup ⟨1, by decide⟩), .push 5 0x01000003d0, .op .NOT,
   .op .EQ, .op .OR]

def primeProgram : List Instr :=
  primeValueProgram ++ WindowTwentyOneEntry.testProgram (UInt256.ofNat 1773)

theorem run_load (template : State) (offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[5]? = some offset) :
    runInstructions loadProgram (framed template (UInt256.ofNat 42) rest) =
    some (framed template (UInt256.ofNat 45)
      (MachineState.readWord template.executionEnv.calldata offset.toNat :: rest)) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  simp [loadProgram, runInstructions, framed, hoff, hc0, hc1,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_exponent (template : State) (modulus offset : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999) (hoff : rest[4]? = some offset)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 1773 = true) :
    runInstructions exponentProgram (framed template (UInt256.ofNat 45) (modulus :: rest)) =
    some (framed template
      (if (UInt256.xor (modulus - UInt256.ofNat 1)
        (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0
        then UInt256.ofNat 56 else UInt256.ofNat 1773)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  by_cases hz : (UInt256.xor (modulus - UInt256.ofNat 1)
      (MachineState.readWord template.executionEnv.calldata offset.toNat)).toNat = 0 <;>
    simp [exponentProgram, runInstructions, framed, hoff, hc1, hc2, hc3, hc4,
      htarget, hz, UInt256.isTrue, Challenge.EvmProof.Stepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_prime (template : State) (modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 999)
    (htarget : Decode.isValidJumpDest template.executionEnv.code 1773 = true) :
    runInstructions primeProgram (framed template (UInt256.ofNat 56) (modulus :: rest)) =
    some (framed template
      (if (FermatProgram.primeValue modulus).toNat = 0
        then UInt256.ofNat 1773 else UInt256.ofNat 106)
      (modulus :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hsecp : UInt256.lnot (4294968272 : UInt256) = FermatProgram.secp := by decide
  have hv : runInstructions primeValueProgram
      (framed template (UInt256.ofNat 56) (modulus :: rest)) =
      some (framed template (UInt256.ofNat 101)
        (FermatProgram.primeValue modulus :: modulus :: rest)) := by
    simp (config := { maxSteps := 500000 })
      [primeValueProgram, FermatProgram.primeValue, runInstructions, framed,
        Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hc3, hc4, hsecp,
        Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have ht := WindowTwentyOneEntry.run_test template (UInt256.ofNat 101)
    (UInt256.ofNat 1773) (FermatProgram.primeValue modulus) (modulus :: rest)
    (by simp; omega) htarget
  have both := runInstructions_append_some _ _ _ _ _ hv ht
  have hpc : advancePC 5 (UInt256.ofNat 101) = UInt256.ofNat 106 := by decide
  simpa only [primeProgram, hpc, framed] using both

structure Paths (artifact : Challenge.EvmProof.ProgramArtifact) (fork : Fork) where
  load : WindowTwentyOneBinding.Block artifact fork 42 loadProgram
  exponent : WindowTwentyOneBinding.Block artifact fork 45 exponentProgram
  prime : WindowTwentyOneBinding.Block artifact fork 56 primeProgram
  result : WindowTwentyOneBinding.Block artifact fork 106 FermatProgram.returnProgram
  legacyJump : Decode.isValidJumpDest artifact.code 1773 = true

#print axioms run_load
#print axioms run_exponent
#print axioms run_prime
end Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

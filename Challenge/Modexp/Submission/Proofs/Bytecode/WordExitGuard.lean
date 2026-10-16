import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordExitGuard
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .EQ, .push 2 5554, .op .JUMPI]

def frame (s : State) (pc : UInt256) (e acc base modulus bsize : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc, stack := [e, acc, base, modulus, bsize, e] ++ rest }

set_option linter.unusedSimpArgs false in
/-- Prove the taken exit with symbolic code; the caller supplies the exact
artifact's jump-destination certificate without unfolding that byte array. -/
theorem run (s : State) (e acc base modulus bsize : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 5554 = true) :
    runInstructions program (frame s (UInt256.ofNat 194) e acc base modulus bsize rest) =
      some (frame s (UInt256.ofNat 5554) e acc base modulus bsize rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdestWord : (5554 : UInt256).toNat = 5554 := by decide
  simp [program, frame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    Nat.add_assoc, hc6, hc7, hc8, hdest, hdestWord, UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WordExitGuard

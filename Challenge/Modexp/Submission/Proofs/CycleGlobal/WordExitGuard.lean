import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace CycleSubmission.Global.WordExitGuard
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def program : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .EQ, .push 2 3976, .op .JUMPI]

def frame (s : State) (pc : UInt256) (e acc base modulus bsize : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := pc, stack := [e, acc, base, modulus, bsize, e] ++ rest }

set_option linter.unusedSimpArgs false in
/-- Prove the taken exit with symbolic code; the caller supplies the exact
artifact's jump-destination certificate without unfolding that byte array. -/
theorem run (s : State) (e acc base modulus bsize : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hdest : Decode.isValidJumpDest s.executionEnv.code 3976 = true) :
    runInstructions program (frame s (UInt256.ofNat 194) e acc base modulus bsize rest) =
      some (frame s (UInt256.ofNat 3976) e acc base modulus bsize rest) := by
  have capacity (j : Nat) (hj : j ≤ 8) : rest.length + j < 1024 := by omega
  have hdestWord : (3976 : UInt256).toNat = 3976 := by decide
  simp [program, frame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    Nat.add_assoc, capacity, Nat.add_assoc, hdest, hdestWord, UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end CycleSubmission.Global.WordExitGuard

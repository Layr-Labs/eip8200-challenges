import Challenge.Ripemd160.Submission.Local20261028.RecArmsLong
import Challenge.Ripemd160.Submission.Local20261028.RecPatterned128Entry
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

/-!
# Size dispatch into the compact arms

The short size table selects a three-byte trampoline (or the one-byte arm
directly); 256 and 376 bytes are matched by equality.  Every allowed size other
than 1000 reaches its arm and returns RIPEMD-160.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open StackRoundTrace StackRoundTemplate J2Moves ReverseLiteralRaw
open Arms.Scan

def trampTemplate (target : Nat) : List Instr := [.op .JUMPDEST] ++ jumpTemplate target

theorem run_tramp (input : ByteArray) (pc target : Nat) (ht : target < 2^256)
    (hv : Decode.isValidJumpDest Control.Artifact.submissionArtifact.code target = true) :
    runInstrSeq (trampTemplate target) (atState (base input) pc []) =
      some (atState (base input) target []) := by
  have h1 := run_jd (base input) (UInt256.ofNat pc) [] (by simp) rfl
  have h2 := run_jump (base input) (pcAfter (UInt256.ofNat pc) [.op .JUMPDEST]) target [] (by simp) rfl
    (by rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt ht]; exact hv)
  exact DenseScheduleTrace.runInstrSeq_append_running h1 rfl h2


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Arms.Dispatch

import Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps
import Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheExitTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCachedMacCore

def normalGuard : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 2 4268, .op .EQ, .push 2 4208, .op .JUMPI]

def drop : List Instr := GenericReturnAdapter.retainFrame2DUP16Program

theorem run_guard (s : State) (pc : Nat)
    (pbi pb ent tn target inv : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions normalGuard
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi (UInt256.ofNat 3543) pb ent tn target inv rest)) =
    some (framed s (UInt256.ofNat (pc+9))
      (TnCacheFrameOps.frame pbi (UInt256.ofNat 3543) pb ent tn target inv rest)) := by
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h4471 : (4268 : UInt256).toNat = 4268 := by decide
  simp [normalGuard, TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, h8, h9, h10,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, UInt256.eq, UInt256.isTrue, h4471]

theorem run_drop (s : State) (pc : Nat)
    (pbi hd pb ent tn target inv m0 tl m96 m64 m32 aEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hjump : Decode.isValidJumpDest s.executionEnv.code
      GenericReturnAdapter.sharedCleanupNextPC = true) :
    runInstructions drop
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi hd pb ent tn target inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) =
    some (framed s (UInt256.ofNat GenericReturnAdapter.sharedCleanupNextPC)
      (dst :: ret :: TnCacheFrameOps.frame pbi hd pb ent tn target inv
        (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  simp [drop, GenericReturnAdapter.retainFrame2DUP16Program,
    TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, h16, h17, h18, h19,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  simpa [GenericReturnAdapter.sharedCleanupNextPC] using hjump

theorem run_square_guard (s : State) (pc : Nat)
    (pbi pb ent tn target inv : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hj : Decode.isValidJumpDest s.executionEnv.code 4208 = true) :
    runInstructions normalGuard
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi (UInt256.ofNat 4268) pb ent tn target inv rest)) =
    some (framed s (UInt256.ofNat 4208)
      (TnCacheFrameOps.frame pbi (UInt256.ofNat 4268) pb ent tn target inv rest)) := by
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h4471 : (4268 : UInt256).toNat = 4268 := by decide
  have h4362 : (4208 : UInt256).toNat = 4208 := by decide
  have ht : (4208 : UInt256) = UInt256.ofNat 4208 := by decide
  simp [normalGuard, TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, h8, h9, h10,
    UInt256.eq, UInt256.isTrue, h4471, h4362, ht, hj]

#print axioms run_guard
#print axioms run_drop
#print axioms run_square_guard
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheExitTrace

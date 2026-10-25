import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheFrameOps

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace CycleSubmission.Global.Fast.TnCacheExitTrace
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast CiosCachedMacCore

def normalGuard : List Instr :=
  [.push 4 0, .op .POP, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]


def drop : List Instr := List.replicate 14 (.op .POP)

/-- Fixed-width no-op replaces the multiply-only guard; preserve its caller contract. -/

theorem run_guard (s : State) (pc hd : Nat) (hhd : hd = 3775)
    (pbi pb ent tn target inv : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions normalGuard
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi (UInt256.ofNat hd) pb ent tn target inv rest)) =
    some (framed s (UInt256.ofNat (pc+9))
      (TnCacheFrameOps.frame pbi (UInt256.ofNat hd) pb ent tn target inv rest)) := by
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h4471 : (5297 : UInt256).toNat = 5297 := by decide
  subst hd
 
  simp [normalGuard, TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, h8, h9, h10,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Nat.add_assoc, UInt256.eq, UInt256.isTrue, h4471]


theorem run_drop (s : State) (pc : Nat)
    (pbi hd pb ent tn target inv m0 tl m96 m64 m32 aEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions drop
      (framed s (UInt256.ofNat pc)
        (TnCacheFrameOps.frame pbi hd pb ent tn target inv
          (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest))) =
    some (framed s (UInt256.ofNat (pc+14)) (dst :: ret :: rest)) := by
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  have h16 : rest.length+16 < 1024 := by omega
  simp [drop, List.replicate, TnCacheFrameOps.frame, framed, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]


end CycleSubmission.Global.Fast.TnCacheExitTrace

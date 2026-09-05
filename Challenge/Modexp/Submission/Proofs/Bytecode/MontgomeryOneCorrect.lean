import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open MontgomeryOneBlock
open Challenge.Modexp (submissionBytecode)

-- Exact canonical leaf bridges to the accepted Task16 model.
theorem clearLeaf_eq (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) :
    clearLeaf s n = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.clearLeaf s 7168 n ret saved := rfl

theorem seedLeaf_eq (s : State) :
    seedLeaf s = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.storeOneLeaf s 7168 := rfl

theorem reduceLeaf_eq (s : State) (n : Nat) (high ret : UInt256) (saved : List UInt256) :
    reduceLeaf s n high = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.reduceLeaf s 7168 0 high n ret saved := rfl

theorem doubleLeaf_eq (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256) :
    doubleLeaf s n = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleLeaf s 7168 0 n ret saved := rfl

theorem progress_eq (s : State) (n i : Nat) (ret : UInt256) (saved : List UInt256) :
    progress s n i = Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress s 7168 0 n ret saved i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [progress, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.doubleProgress, ih, doubleLeaf_eq]

theorem returned_eq_makeMontgomeryOne (s : State) (n : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32) :
    returned s n ret saved =
      { s with pc := ret
               stack := saved
               memory := (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne s 0 n ret saved).memory
               activeWords := (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne s 0 n ret saved).activeWords } := by
  have hreduce (q : State) (k : Nat) (high : UInt256) :=
    reduceLeaf_eq q k high ret saved
  have hprogress (q : State) (k i : Nat) := progress_eq q k i ret saved
  unfold returned
  dsimp only
  rw [touched_clear s n hn hN]
  simp only [clearLeaf_eq s n ret saved, top, hreduce, seedLeaf_eq, hprogress,
    Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne, Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.unit, Nat.zero_add]
  rfl

theorem returned_correct (s : State) (n m : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hmR : m < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) (hodd : m % 2 = 1)
    (hmod : Limbs.Represents s.memory 0 n m) :
    Limbs.Represents (returned s n ret saved).memory 7168 n (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n % m) ∧
      Limbs.Represents (returned s n ret saved).memory 0 n m := by
  rw [returned_eq_makeMontgomeryOne s n ret saved hn hN]
  exact Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne_correct s n m hn hN hm hmR hodd hmod ret saved

theorem returned_preserves_region (s : State) (n m ptr value : Nat)
    (ret : UInt256) (saved : List UInt256) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hm : 0 < m) (hmR : m < Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.R n) (hodd : m % 2 = 1)
    (hmod : Limbs.Represents s.memory 0 n m)
    (hdisjoint : Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.DisjointSetup n ptr)
    (hrep : Limbs.Represents s.memory ptr n value) :
    Limbs.Represents (returned s n ret saved).memory ptr n value := by
  rw [returned_eq_makeMontgomeryOne s n ret saved hn hN]
  exact Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne_preserves_region s n m ptr value
    hn hN hm hmR hodd hmod hdisjoint hrep ret saved

def gasSteps_makeMontgomeryOne (s : State) (n : Nat) (ret : UInt256) (saved : List UInt256)
    (hcap : saved.length < 996) (hn : 1 ≤ n) (hN : n ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    GasSteps (entry s n ret saved)
      { s with pc := ret
               stack := saved
               memory := (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne s 0 n ret saved).memory
               activeWords := (Challenge.Modexp.Submission.Proofs.Montgomery.OneMemory.makeMontgomeryOne s 0 n ret saved).activeWords } :=
  (gasSteps_unit s n ret saved hcap hn hN hcode hfork hrun hnp hret).cast rfl
    (returned_eq_makeMontgomeryOne s n ret saved hn hN)

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryOneCorrect

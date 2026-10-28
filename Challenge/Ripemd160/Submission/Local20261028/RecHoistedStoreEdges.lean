import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreSites
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreEdges
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate HoistedStoreResearch HoistedStoreSites

def gasSteps_branch_zero (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) :
    GasSteps {s with pc := UInt256.ofNat 9934, stack := (0 : UInt256) :: rho}
      {s with pc := UInt256.ofNat 9938, stack := rho} := by
  apply lift .branch s _ e _
  simpa only [template, pc, show (0 : UInt256).toNat = 0 by decide,
    ne_eq, not_true_eq_false, if_false] using
    run_terminalBranch s 0 rho (by omega) e.run (by rw [e.code]; exact valid_miss)

#print axioms gasSteps_branch_zero

def gasSteps_branch_nonzero (s : State) (c : UInt256) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (hn : c.toNat ≠ 0) :
    GasSteps {s with pc := UInt256.ofNat 9934, stack := c :: rho}
      {s with pc := UInt256.ofNat 9941, stack := rho} := by
  apply lift .branch s _ e _
  simpa only [template, pc, if_pos hn] using
    run_terminalBranch s c rho (by omega) e.run (by rw [e.code]; exact valid_miss)

#print axioms gasSteps_branch_nonzero

def gasSteps_return (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 1) :
    GasSteps {s with pc := UInt256.ofNat 9938, stack := rho}
      {s with pc := UInt256.ofNat 9940, stack := rho, halt := .Returned, hReturn := MachineState.readPadded s.memory 0 32} :=
  lift .success s _ e _ (run_success s rho (by omega) e.run ha)

#print axioms gasSteps_return

def gasSteps_miss_jump (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) :
    GasSteps {s with pc := UInt256.ofNat 9941, stack := rho}
      {s with pc := UInt256.ofNat 8078, stack := (0 : UInt256) :: rho} :=
  lift .miss s _ e _ (run_miss s rho (by omega) e.run (by rw [e.code]; exact valid_cleanup))

#print axioms gasSteps_miss_jump

def gasSteps_cleanup (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (ha : s.activeWords = UInt256.ofNat 1) :
    GasSteps {s with pc := UInt256.ofNat 8078, stack := rho}
      (RetainedResultEdge112.cleared s rho) :=
  lift .cleanup s _ e _ (HoistedStoreResearch.run_cleanup_relocated s rho (by omega)
    e.run ha (by rw [e.code]; exact valid_generic))

#print axioms gasSteps_cleanup

def gasSteps_copy (s : State) (rho : List UInt256) (e : Env s)
    (hs : rho.length ≤ 976) (hfit : s.executionEnv.calldata.size < 2 ^ 256)
    (hpos : 0 < s.executionEnv.calldata.size) (hm : s.memory.size = 32) :
    GasSteps (RetainedResultEdge112.cleared s rho) (RetainedFallback114.copied s rho) := by
  let cleared := RetainedResultEdge112.cleared s rho
  have ec : Env cleared := ⟨e.code, e.fork, e.run, e.np⟩
  exact lift .copy cleared _ ec _
    (RetainedFallback114.run_copy s rho (by omega) e.run hfit hpos hm)

#print axioms gasSteps_copy
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreEdges

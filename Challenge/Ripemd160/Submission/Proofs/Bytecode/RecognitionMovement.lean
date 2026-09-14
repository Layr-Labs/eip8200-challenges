import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFrame
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionMovement
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace RecognitionSites RecognitionBodyRaw RecognitionFrame

def gasSteps_normal (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 184 (frame f rho)) (atState s 207 (frame (RecognitionBodyRaw.normalResult s f) rho)) := by
  apply normal.lift s _ e (frame f rho)
  have h := RecognitionFundedBodyRaw.run_normal s (UInt256.ofNat 184) f rho hs e.run
  simpa only [atState, normal.end_pc] using h
def gasSteps_boundary (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 221 (frame f rho)) (atState s 274 (frame (RecognitionBodyRaw.boundaryResult s f) rho)) := by
  apply boundary.lift s _ e (frame f rho)
  have h := RecognitionFundedBodyRaw.run_boundary s (UInt256.ofNat 221) f rho hs e.run
  simpa only [atState, boundary.end_pc] using h
def gasSteps_partial (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 294 (frame f rho)) (atState s 310 (frame (RecognitionControlRaw.partialResult s f) rho)) := by
  apply partialWord.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_partial s (UInt256.ofNat 294) f rho hs e.run
  simpa only [atState, partialWord.end_pc] using h
def gasSteps_reset0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 174 (frame f rho)) (atState s 177 (frame ({f with stop := f.full}) rho)) := by
  apply reset0.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 174) f rho hs e.run
  simpa only [atState, reset0.end_pc] using h

def gasSteps_reset (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 280 (frame f rho)) (atState s 283 (frame ({f with stop := f.full}) rho)) := by
  apply reset.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 280) f rho hs e.run
  simpa only [atState, reset.end_pc] using h
def gasSteps_init (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 111 rho)
      (atState s 168 (frame (RecognitionControlRaw.initResult s.executionEnv.calldata.size) rho)) := by
  apply init.lift s _ e rho
  have h := RecognitionControlRaw.run_init_body s (UInt256.ofNat 111) rho hs e.run
  simpa only [atState, init.end_pc] using h

def gasSteps_test0_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ f.off.toNat = f.stop.toNat) :
    GasSteps (atState s 178 (frame f rho)) (atState s 184 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_head s (UInt256.ofNat 178) f rho 213 hs e.run (valid_214 s e)
  simpa only [atState, test0.end_pc, if_neg hc] using h
def gasSteps_test0_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat = f.stop.toNat) :
    GasSteps (atState s 178 (frame f rho)) (atState s 213 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_head s (UInt256.ofNat 178) f rho 213 hs e.run (valid_214 s e)
  simpa only [atState, test0.end_pc, if_pos hc] using h
def gasSteps_test_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat < f.stop.toNat) :
    GasSteps (atState s 207 (frame f rho)) (atState s 184 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_continue s (UInt256.ofNat 207) f rho 184 hs e.run hc (valid_185 s e)
  simpa only [atState, test.end_pc] using h
def gasSteps_test_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.stop.toNat ≤ f.off.toNat) :
    GasSteps (atState s 207 (frame f rho)) (atState s 213 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_exit s (UInt256.ofNat 207) f rho 184 hs e.run hc
  simpa only [atState, test.end_pc] using h
def gasSteps_segment_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ f.off.toNat < f.full.toNat)
    (hbound : f.off.toNat ≤ f.full.toNat) :
    GasSteps (atState s 213 (frame f rho)) (atState s 286 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 213) f rho 286 hs e.run (valid_291 s e)
  have heq : f.off.toNat = f.full.toNat := by omega
  simpa only [atState, segment.end_pc, if_pos heq] using h
def gasSteps_segment_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (¬ f.off.toNat < f.full.toNat))
    (_hbound : f.off.toNat ≤ f.full.toNat) :
    GasSteps (atState s 213 (frame f rho)) (atState s 221 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 213) f rho 286 hs e.run (valid_291 s e)
  have hne : ¬ f.off.toNat = f.full.toNat := by omega
  simpa only [atState, segment.end_pc, if_neg hne] using h
def gasSteps_partialBranch_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat = s.executionEnv.calldata.size % 2^256) :
    GasSteps (atState s 286 (frame f rho)) (atState s 310 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 286) f rho 310 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_pos hc] using h
def gasSteps_partialBranch_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.off.toNat = s.executionEnv.calldata.size % 2^256)) :
    GasSteps (atState s 286 (frame f rho)) (atState s 294 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 286) f rho 310 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_neg hc] using h
def gasSteps_finish_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.acc.toNat = 0) :
    GasSteps (atState s 310 (frame f rho)) (atState s 315 (RecognitionBranchRaw.finishRest f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 310) f rho 342 hs e.run (valid_342 s e)
  simpa only [atState, finish.end_pc, if_pos hc] using h
def gasSteps_finish_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.acc.toNat = 0)) :
    GasSteps (atState s 310 (frame f rho)) (atState s 342 (RecognitionBranchRaw.finishRest f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 310) f rho 342 hs e.run (valid_342 s e)
  simpa only [atState, finish.end_pc, if_neg hc] using h
def gasSteps_cleanup (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 342 (RecognitionBranchRaw.finishRest f rho)) (atState s 351 rho) := by
  apply cleanup.lift s _ e (RecognitionBranchRaw.finishRest f rho)
  have h := RecognitionControlSimplify.run_cleanup s (UInt256.ofNat 342) f rho hs e.run
  simpa only [atState, cleanup.end_pc] using h

def gasSteps_clamp0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 168 (frame f rho)) (atState s 177 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp s (UInt256.ofNat 168) f rho 177 hs e.run (valid_174 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp0.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 168 (frame f rho))
        (atState s 174 (frame f rho)) := by
      apply clamp0.lift s _ e (frame f rho)
      simpa only [atState, clamp0.end_pc, if_neg hc] using h
    simpa only [RecognitionFrame.clamp, if_neg hc] using g.trans (gasSteps_reset0 s e f rho hs)

def gasSteps_back (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 283 (frame f rho)) (atState s 177 (frame f rho)) := by
  apply back.lift s _ e (frame f rho)
  have hv : Decode.isValidJumpDest s.executionEnv.code 177 = true := by
    simpa only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using valid_175 s e
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, back.template, frame, runInstrSeq, DataStepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv]

def gasSteps_clamp (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 274 (frame f rho)) (atState s 177 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp_width 1 (by decide) s (UInt256.ofNat 274) f rho 177 hs e.run (valid_175 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 274 (frame f rho))
      (atState s 280 (frame f rho)) := by
      apply clamp.lift s _ e (frame f rho)
      simpa only [atState, clamp.end_pc, if_neg hc] using h
    have gb := (g.trans (gasSteps_reset s e f rho hs)).trans (gasSteps_back s e ({ f with stop := f.full }) rho hs)
    simpa only [RecognitionFrame.clamp, if_neg hc] using gb
def gasSteps_pass0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 177 (frame f rho)) (atState s 178 (frame f rho)) := by
  apply pass0.lift s _ e (frame f rho)
  have h := RecognitionControlSimplify.run_pass s (UInt256.ofNat 177) (frame f rho)
    (by simp [frame]; omega) e.run
  simpa only [atState, pass0.end_pc] using h

def gasSteps_pass (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 177 (frame f rho)) (atState s 178 (frame f rho)) := by
  apply pass.lift s _ e (frame f rho)
  have h := RecognitionControlSimplify.run_pass s (UInt256.ofNat 177) (frame f rho)
    (by simp [frame]; omega) e.run
  simpa only [atState, pass.end_pc] using h


#print axioms gasSteps_init
#print axioms gasSteps_normal
#print axioms gasSteps_boundary
#print axioms gasSteps_cleanup
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionMovement

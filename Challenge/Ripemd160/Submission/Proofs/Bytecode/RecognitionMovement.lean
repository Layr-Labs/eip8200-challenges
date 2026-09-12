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
    GasSteps (atState s 185 (frame f rho)) (atState s 208 (frame (RecognitionBodyRaw.normalResult s f) rho)) := by
  apply normal.lift s _ e (frame f rho)
  have h := RecognitionBodyRaw.run_normal s (UInt256.ofNat 185) f rho hs e.run
  simpa only [atState, normal.end_pc] using h

def gasSteps_boundary (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 223 (frame f rho)) (atState s 277 (frame (RecognitionBodyRaw.boundaryResult s f) rho)) := by
  apply boundary.lift s _ e (frame f rho)
  have h := RecognitionBodyRaw.run_boundary s (UInt256.ofNat 223) f rho hs e.run
  simpa only [atState, boundary.end_pc] using h

def gasSteps_partial (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 299 (frame f rho)) (atState s 315 (frame (RecognitionControlRaw.partialResult s f) rho)) := by
  apply partialWord.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_partial s (UInt256.ofNat 299) f rho hs e.run
  simpa only [atState, partialWord.end_pc] using h

def gasSteps_reset0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 171 (frame f rho)) (atState s 174 (frame ({f with stop := f.full}) rho)) := by
  apply reset0.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 171) f rho hs e.run
  simpa only [atState, reset0.end_pc] using h

def gasSteps_reset (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 284 (frame f rho)) (atState s 287 (frame ({f with stop := f.full}) rho)) := by
  apply reset.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 284) f rho hs e.run
  simpa only [atState, reset.end_pc] using h

def gasSteps_init (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 108 rho)
      (atState s 165 (frame (RecognitionControlRaw.initResult s.executionEnv.calldata.size) rho)) := by
  apply init.lift s _ e rho
  have h := RecognitionControlRaw.run_init_body s (UInt256.ofNat 108) rho hs e.run
  simpa only [atState, init.end_pc] using h

def gasSteps_test0_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat < f.stop.toNat) :
    GasSteps (atState s 176 (frame f rho)) (atState s 185 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_continue s (UInt256.ofNat 176) f rho 185 hs e.run hc (valid_185 s e)
  simpa only [atState, test0.end_pc] using h

def gasSteps_test0_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.stop.toNat ≤ f.off.toNat) :
    GasSteps (atState s 176 (frame f rho)) (atState s 182 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_exit s (UInt256.ofNat 176) f rho 185 hs e.run hc
  simpa only [atState, test0.end_pc] using h

def gasSteps_test_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat < f.stop.toNat) :
    GasSteps (atState s 208 (frame f rho)) (atState s 185 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_continue s (UInt256.ofNat 208) f rho 185 hs e.run hc (valid_185 s e)
  simpa only [atState, test.end_pc] using h

def gasSteps_test_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.stop.toNat ≤ f.off.toNat) :
    GasSteps (atState s 208 (frame f rho)) (atState s 214 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_exit s (UInt256.ofNat 208) f rho 185 hs e.run hc
  simpa only [atState, test.end_pc] using h

def gasSteps_segment_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ f.off.toNat < f.full.toNat) :
    GasSteps (atState s 214 (frame f rho)) (atState s 291 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 214) f rho 291 hs e.run (valid_291 s e)
  simpa only [atState, segment.end_pc, if_pos hc] using h

def gasSteps_segment_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (¬ f.off.toNat < f.full.toNat)) :
    GasSteps (atState s 214 (frame f rho)) (atState s 223 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 214) f rho 291 hs e.run (valid_291 s e)
  simpa only [atState, segment.end_pc, if_neg hc] using h

def gasSteps_partialBranch_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat = s.executionEnv.calldata.size % 2^256) :
    GasSteps (atState s 291 (frame f rho)) (atState s 315 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 291) f rho 315 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_pos hc] using h

def gasSteps_partialBranch_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.off.toNat = s.executionEnv.calldata.size % 2^256)) :
    GasSteps (atState s 291 (frame f rho)) (atState s 299 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 291) f rho 315 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_neg hc] using h

def gasSteps_finish_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.acc.toNat = 0) :
    GasSteps (atState s 315 (frame f rho)) (atState s 4793 (frame f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 315) f rho 4793 hs e.run (valid_4796 s e)
  simpa only [atState, finish.end_pc, if_pos hc] using h

def gasSteps_finish_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.acc.toNat = 0)) :
    GasSteps (atState s 315 (frame f rho)) (atState s 322 (frame f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 315) f rho 4793 hs e.run (valid_4796 s e)
  simpa only [atState, finish.end_pc, if_neg hc] using h

def gasSteps_cleanup (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 322 (frame f rho)) (atState s 335 rho) := by
  apply cleanup.lift s _ e (frame f rho)
  exact RecognitionBranchRaw.run_cleanup s (UInt256.ofNat 322) f rho 335 hs e.run (valid_335 s e)

def gasSteps_clamp0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 165 (frame f rho)) (atState s 174 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp s (UInt256.ofNat 165) f rho 174 hs e.run (valid_174 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp0.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 165 (frame f rho))
        (atState s 171 (frame f rho)) := by
      apply clamp0.lift s _ e (frame f rho)
      simpa only [atState, clamp0.end_pc, if_neg hc] using h
    simpa only [RecognitionFrame.clamp, if_neg hc] using g.trans (gasSteps_reset0 s e f rho hs)

def gasSteps_clamp (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 277 (frame f rho)) (atState s 287 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp_width 2 (by decide) s (UInt256.ofNat 277) f rho 287 hs e.run (valid_287 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 277 (frame f rho))
        (atState s 284 (frame f rho)) := by
      apply clamp.lift s _ e (frame f rho)
      simpa only [atState, clamp.end_pc, if_neg hc] using h
    simpa only [RecognitionFrame.clamp, if_neg hc] using g.trans (gasSteps_reset s e f rho hs)

def gasSteps_pass0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 174 (frame f rho)) (atState s 176 (frame f rho)) := by
  apply pass0.lift s _ e (frame f rho)
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, pass0.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  decide

def gasSteps_pass (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 175 (frame f rho)) (atState s 176 (frame f rho)) := by
  apply pass.lift s _ e (frame f rho)
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, pass.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  decide

def gasSteps_skip (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 182 (frame f rho)) (atState s 214 (frame f rho)) := by
  apply skip.lift s _ e (frame f rho)
  have hv : Decode.isValidJumpDest s.executionEnv.code 214 = true := by
    simpa only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using valid_214 s e
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, skip.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv]

def gasSteps_back (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 287 (frame f rho)) (atState s 175 (frame f rho)) := by
  apply back.lift s _ e (frame f rho)
  have hv : Decode.isValidJumpDest s.executionEnv.code 175 = true := by
    simpa only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using valid_175 s e
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, back.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv]

#print axioms gasSteps_init
#print axioms gasSteps_normal
#print axioms gasSteps_boundary
#print axioms gasSteps_cleanup
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionMovement

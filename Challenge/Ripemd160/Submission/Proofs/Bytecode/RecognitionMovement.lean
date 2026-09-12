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
    GasSteps (atState s 186 (frame f rho)) (atState s 209 (frame (RecognitionBodyRaw.normalResult s f) rho)) := by
  apply normal.lift s _ e (frame f rho)
  have h := RecognitionBodyRaw.run_normal s (UInt256.ofNat 186) f rho hs e.run
  simpa only [atState, normal.end_pc] using h

def gasSteps_boundary (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 224 (frame f rho)) (atState s 278 (frame (RecognitionBodyRaw.boundaryResult s f) rho)) := by
  apply boundary.lift s _ e (frame f rho)
  have h := RecognitionBodyRaw.run_boundary s (UInt256.ofNat 224) f rho hs e.run
  simpa only [atState, boundary.end_pc] using h

def gasSteps_partial (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 300 (frame f rho)) (atState s 316 (frame (RecognitionControlRaw.partialResult s f) rho)) := by
  apply partialWord.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_partial s (UInt256.ofNat 300) f rho hs e.run
  simpa only [atState, partialWord.end_pc] using h

def gasSteps_reset0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 172 (frame f rho)) (atState s 175 (frame ({f with stop := f.full}) rho)) := by
  apply reset0.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 172) f rho hs e.run
  simpa only [atState, reset0.end_pc] using h

def gasSteps_reset (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 285 (frame f rho)) (atState s 288 (frame ({f with stop := f.full}) rho)) := by
  apply reset.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_reset s (UInt256.ofNat 285) f rho hs e.run
  simpa only [atState, reset.end_pc] using h

def gasSteps_init (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 109 rho)
      (atState s 166 (frame (RecognitionControlRaw.initResult s.executionEnv.calldata.size) rho)) := by
  apply init.lift s _ e rho
  have h := RecognitionControlRaw.run_init_body s (UInt256.ofNat 109) rho hs e.run
  simpa only [atState, init.end_pc] using h

def gasSteps_test0_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat < f.stop.toNat) :
    GasSteps (atState s 177 (frame f rho)) (atState s 186 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_continue s (UInt256.ofNat 177) f rho 186 hs e.run hc (valid_185 s e)
  simpa only [atState, test0.end_pc] using h

def gasSteps_test0_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.stop.toNat ≤ f.off.toNat) :
    GasSteps (atState s 177 (frame f rho)) (atState s 183 (frame f rho)) := by
  apply test0.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_exit s (UInt256.ofNat 177) f rho 186 hs e.run hc
  simpa only [atState, test0.end_pc] using h

def gasSteps_test_continue (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat < f.stop.toNat) :
    GasSteps (atState s 209 (frame f rho)) (atState s 186 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_continue s (UInt256.ofNat 209) f rho 186 hs e.run hc (valid_185 s e)
  simpa only [atState, test.end_pc] using h

def gasSteps_test_exit (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.stop.toNat ≤ f.off.toNat) :
    GasSteps (atState s 209 (frame f rho)) (atState s 215 (frame f rho)) := by
  apply test.lift s _ e (frame f rho)
  have h := RecognitionControlRaw.run_test_exit s (UInt256.ofNat 209) f rho 186 hs e.run hc
  simpa only [atState, test.end_pc] using h

def gasSteps_segment_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ f.off.toNat < f.full.toNat) :
    GasSteps (atState s 215 (frame f rho)) (atState s 292 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 215) f rho 292 hs e.run (valid_291 s e)
  simpa only [atState, segment.end_pc, if_pos hc] using h

def gasSteps_segment_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (¬ f.off.toNat < f.full.toNat)) :
    GasSteps (atState s 215 (frame f rho)) (atState s 224 (frame f rho)) := by
  apply segment.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_segment s (UInt256.ofNat 215) f rho 292 hs e.run (valid_291 s e)
  simpa only [atState, segment.end_pc, if_neg hc] using h

def gasSteps_partialBranch_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.off.toNat = s.executionEnv.calldata.size % 2^256) :
    GasSteps (atState s 292 (frame f rho)) (atState s 316 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 292) f rho 316 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_pos hc] using h

def gasSteps_partialBranch_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.off.toNat = s.executionEnv.calldata.size % 2^256)) :
    GasSteps (atState s 292 (frame f rho)) (atState s 300 (frame f rho)) := by
  apply partialBranch.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_partial s (UInt256.ofNat 292) f rho 316 hs e.run (valid_315 s e)
  simpa only [atState, partialBranch.end_pc, if_neg hc] using h

def gasSteps_finish_yes (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : f.acc.toNat = 0) :
    GasSteps (atState s 316 (frame f rho)) (atState s 4873 (frame f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 316) f rho 4873 hs e.run (valid_4796 s e)
  simpa only [atState, finish.end_pc, if_pos hc] using h

def gasSteps_finish_no (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256)
    (hs : rho.length ≤ 990) (hc : ¬ (f.acc.toNat = 0)) :
    GasSteps (atState s 316 (frame f rho)) (atState s 323 (frame f rho)) := by
  apply finish.lift s _ e (frame f rho)
  have h := RecognitionBranchRaw.run_finish s (UInt256.ofNat 316) f rho 4873 hs e.run (valid_4796 s e)
  simpa only [atState, finish.end_pc, if_neg hc] using h

def gasSteps_cleanup (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 323 (frame f rho)) (atState s 336 rho) := by
  apply cleanup.lift s _ e (frame f rho)
  exact RecognitionBranchRaw.run_cleanup s (UInt256.ofNat 323) f rho 336 hs e.run (valid_335 s e)

def gasSteps_clamp0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 166 (frame f rho)) (atState s 175 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp s (UInt256.ofNat 166) f rho 175 hs e.run (valid_174 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp0.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 166 (frame f rho))
        (atState s 172 (frame f rho)) := by
      apply clamp0.lift s _ e (frame f rho)
      simpa only [atState, clamp0.end_pc, if_neg hc] using h
    simpa only [RecognitionFrame.clamp, if_neg hc] using g.trans (gasSteps_reset0 s e f rho hs)

def gasSteps_clamp (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 278 (frame f rho)) (atState s 288 (frame (RecognitionFrame.clamp f) rho)) := by
  have h := RecognitionBranchRaw.run_clamp_width 2 (by decide) s (UInt256.ofNat 278) f rho 288 hs e.run (valid_287 s e)
  by_cases hc : f.stop.toNat < f.full.toNat
  · apply clamp.lift s _ e (frame f rho)
    simpa only [atState, RecognitionFrame.clamp, if_pos hc] using h
  · have g : GasSteps (atState s 278 (frame f rho))
        (atState s 285 (frame f rho)) := by
      apply clamp.lift s _ e (frame f rho)
      simpa only [atState, clamp.end_pc, if_neg hc] using h
    simpa only [RecognitionFrame.clamp, if_neg hc] using g.trans (gasSteps_reset s e f rho hs)

def gasSteps_pass0 (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 175 (frame f rho)) (atState s 177 (frame f rho)) := by
  apply pass0.lift s _ e (frame f rho)
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, pass0.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  decide

def gasSteps_pass (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 176 (frame f rho)) (atState s 177 (frame f rho)) := by
  apply pass.lift s _ e (frame f rho)
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, pass.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  decide

def gasSteps_skip (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 183 (frame f rho)) (atState s 215 (frame f rho)) := by
  apply skip.lift s _ e (frame f rho)
  have hv : Decode.isValidJumpDest s.executionEnv.code 215 = true := by
    simpa only [Word.word_toNat_ofNat, Nat.reducePow, Nat.reduceMod] using valid_214 s e
  have hcap (n : Nat) (hn : n ≤ 30) : rho.length + n < 1024 := by omega
  simp (discharger := omega) [atState, skip.template, frame, runInstrSeq, Stepper.runInstr,
    pcAfter, UInt256.succ, Instr.size, List.exchange, List.getElem?_cons_zero,
    Nat.add_assoc, e.run, hcap, Word.word_toNat_ofNat, Word.literal_eq_ofNat, hv]

def gasSteps_back (s : State) (e : Env s) (f : RecognitionBodyRaw.Frame) (rho : List UInt256) (hs : rho.length ≤ 990) :
    GasSteps (atState s 288 (frame f rho)) (atState s 176 (frame f rho)) := by
  apply back.lift s _ e (frame f rho)
  have hv : Decode.isValidJumpDest s.executionEnv.code 176 = true := by
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

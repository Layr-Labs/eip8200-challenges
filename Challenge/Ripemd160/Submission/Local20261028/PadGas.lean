import Challenge.Ripemd160.Submission.Local20261028.PadSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadGas
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof StackRoundTrace

noncomputable def lift (s t : State)
    (hr : s.halt = .Running)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hpc : s.pc = UInt256.ofNat 64)
    (h : runInstrSeq (PadSetup.template ++ PadBody.template) s = some t) : GasSteps s t := by
  rw [PadSites.template_eq] at h
  have split1 := PadTrace.split (by decide) hr h
  let u := Classical.choose split1
  have h1 := (Classical.choose_spec split1).1
  have hu := (Classical.choose_spec split1).2.1
  have h23 := (Classical.choose_spec split1).2.2
  have split2 := PadTrace.split (by decide) hu h23
  let v := Classical.choose split2
  have h2 := (Classical.choose_spec split2).1
  have hv := (Classical.choose_spec split2).2.1
  have h3 := (Classical.choose_spec split2).2.2
  have eu := PadTrace.executionEnv h1
  have ev := (PadTrace.executionEnv h2).trans eu
  have pu : u.pc = UInt256.ofNat 4601 := by
    exact PadTrace.ends_jump_pc hr ((congrArg (fun code => runInstrSeq code s) PadSites.front_last).symm.trans h1)
  have pv : v.pc = UInt256.ofNat 10024 := by
    exact PadTrace.ends_jump_pc hu ((congrArg (fun code => runInstrSeq code u) PadSites.middle_last).symm.trans h2)
  have g1 := PadTrace.gasSteps_of_raw PadSites.frontSite s u hc hf hr hnp
    (hpc.trans PadSites.front_pc.symm) PadSites.front_advances h1
  have g2 := PadTrace.gasSteps_of_raw PadSites.middleSite u v
    (by rw [eu]; exact hc) (by change u.executionEnv.fork = .Osaka; rw [eu]; exact hf)
    hu (by rw [eu]; exact hnp) (pu.trans PadSites.middle_pc.symm) PadSites.middle_advances h2
  have g3 := PadTrace.gasSteps_of_raw PadSites.outputSite v t
    (by rw [ev]; exact hc) (by change v.executionEnv.fork = .Osaka; rw [ev]; exact hf)
    hv (by rw [ev]; exact hnp) (pv.trans PadSites.output_pc.symm) PadSites.output_advances h3
  exact g1.trans (g2.trans g3)

def result (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) : State :=
  PadBody.finalState (PadSetup.prepared s len) len h off limit rho

noncomputable def gasSteps (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 892) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = len)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 64, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho)}
      (result s len h off limit rho) := by
  have hp := PadSetup.run s len (StaggerPersistentFrame.frame h off limit
    (DenseScheduleTemplate.mask8::DenseScheduleTemplate.mask16::rho))
    (by simp [StaggerPersistentFrame.frame]; omega) hr ha hcal
  have hb := PadBody.run (PadSetup.prepared s len) len h off limit rho hs hr ha hcal
    (PadSetup.read s len) (by change Decode.isValidJumpDest s.executionEnv.code 4601 = true; rw [hc]; exact PadSites.valid4601)
    (by change Decode.isValidJumpDest s.executionEnv.code 10024 = true; rw [hc]; exact PadSites.valid10024)
  exact lift _ _ hr hc hf hnp rfl (DenseScheduleTrace.runInstrSeq_append_running hp hr hb)

theorem hReturn_eq (s : State) (len : UInt256) (h : Compression.HashState)
    (off limit : UInt256) (rho : List UInt256) :
    (result s len h off limit rho).hReturn =
      Data.Bytes.natToBytesPadded (Return32Serialize.value (PadFunctional.result len h)).toNat 32 :=
  PadBody.hReturn_eq _ _ _ _ _ _

#print axioms lift
#print axioms gasSteps
#print axioms hReturn_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadGas

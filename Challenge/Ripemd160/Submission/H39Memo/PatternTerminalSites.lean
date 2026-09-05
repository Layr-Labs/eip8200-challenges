import Challenge.Ripemd160.Submission.H39Memo.PatternTerminalCertificates

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTerminalSites

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PatternTerminal PatternTerminalCertificates

abbrev entryPC := PatternTerminalCertificates.entryPC
abbrev entryIndex := PatternTerminalCertificates.entryIndex
abbrev tailOffset := PatternTerminalCertificates.tailOffset

def path (p : Fin 14) : List Located :=
  headPath (headCertificate p) ++
    if h : (PatternFacts.target p).size % 32 ≠ 0 then
      tailPath (tailCertificate p h)
    else []

theorem run_match (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hword : (PatternFacts.target p).size % 32 ≠ 0 →
      MachineState.readWord s.executionEnv.calldata (tailOffset p) = PatternFacts.tailWord p) :
    Stepper.runLocatedBlock (path p) s =
      some (DispatchState.atPC s
        (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)) []) := by
  have hhead := run_head (headCertificate p) s sizeWord hpc hstack hrun
  by_cases hp : (PatternFacts.target p).size % 32 ≠ 0
  · have htail := run_tail (tailCertificate p hp)
      (DispatchState.atPC s (entryPC p + 2) []) rfl rfl hrun hcode
    have htail' : Stepper.runLocatedBlock (tailPath (tailCertificate p hp))
        (DispatchState.atPC s (entryPC p + 2) []) =
        some (DispatchState.atPC s
          (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)) []) := by
      simpa only [DispatchState.atPC, hword hp, if_true, partial_outputPC p hp] using htail
    simp only [path, dif_pos hp]
    exact Stepper.runLocatedBlock_append _ _ _ _ _ hhead hrun htail'
  · simp only [path, dif_neg hp, List.append_nil]
    rw [whole_outputPC p (not_not.mp hp)] at hhead
    exact hhead

theorem run_mismatch (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hp : (PatternFacts.target p).size % 32 ≠ 0)
    (hword : MachineState.readWord s.executionEnv.calldata (tailOffset p) ≠
      PatternFacts.tailWord p) :
    Stepper.runLocatedBlock (path p) s = some (DispatchState.atPC s 1006 []) := by
  have hhead := run_head (headCertificate p) s sizeWord hpc hstack hrun
  have htail := run_tail (tailCertificate p hp)
    (DispatchState.atPC s (entryPC p + 2) []) rfl rfl hrun hcode
  have htail' : Stepper.runLocatedBlock (tailPath (tailCertificate p hp))
      (DispatchState.atPC s (entryPC p + 2) []) =
      some (DispatchState.atPC s 1006 []) := by
    simpa only [DispatchState.atPC, hword, if_false] using htail
  simp only [path, dif_pos hp]
  exact Stepper.runLocatedBlock_append _ _ _ _ _ hhead hrun htail'

theorem run_whole (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hp : (PatternFacts.target p).size % 32 = 0) :
    Stepper.runLocatedBlock (path p) s =
      some (DispatchState.atPC s
        (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)) []) := by
  have hhead := run_head (headCertificate p) s sizeWord hpc hstack hrun
  simp only [path, hp, ne_self_iff_false]
  rw [whole_outputPC p hp] at hhead
  exact hhead

def gasSteps_match (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hword : (PatternFacts.target p).size % 32 ≠ 0 →
      MachineState.readWord s.executionEnv.calldata (tailOffset p) = PatternFacts.tailWord p) :
    GasSteps s (DispatchState.atPC s
      (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)) []) :=
  gasSteps_of_run (path p) (run_match p s sizeWord hpc hstack hrun hcode hword)
    hrun hcode hfork hnp

def gasSteps_mismatch (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hp : (PatternFacts.target p).size % 32 ≠ 0)
    (hword : MachineState.readWord s.executionEnv.calldata (tailOffset p) ≠
      PatternFacts.tailWord p) : GasSteps s (DispatchState.atPC s 1006 []) :=
  gasSteps_of_run (path p) (run_mismatch p s sizeWord hpc hstack hrun hcode hp hword)
    hrun hcode hfork hnp

def gasSteps_whole (p : Fin 14) (s : State) (sizeWord : UInt256)
    (hpc : s.pc = UInt256.ofNat (entryPC p)) (hstack : s.stack = [sizeWord])
    (hrun : s.halt = .Running) (hcode : s.executionEnv.code = h39Bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hp : (PatternFacts.target p).size % 32 = 0) :
    GasSteps s (DispatchState.atPC s
      (TerminalPathsSites.outputPC (PatternFacts.targetIndex p)) []) :=
  gasSteps_of_run (path p) (run_whole p s sizeWord hpc hstack hrun hp)
    hrun hcode hfork hnp

end Challenge.Ripemd160.Submission.H39Memo.PatternTerminalSites

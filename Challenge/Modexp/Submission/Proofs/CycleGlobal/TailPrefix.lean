import Challenge.Modexp.Submission.Proofs.CycleGlobal.TailFourRoute
noncomputable section
set_option maxRecDepth 40000
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.TailPrefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast FixedExponentRoute FixedDirectStates
open CycleSubmission.Global.StackTail
open CycleSubmission CycleSubmission.Global FixedDirectPaths
open CycleSubmission.Global.FixedDirectDispatchTrace CycleSubmission.Global.FixedDirectValueTrace
def gasSteps_entry_three (s : State) (memory : ByteArray)
    (n bsize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (entryState s memory n bsize 3 msize) rho)
      (append (FixedDirectStates.check65537 s memory n bsize 3 msize) rho) :=
  CycleSubmission.Global.StackTail.gasSteps CycleSubmission.Global.FixedDirectPaths.entryPrefix rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_entry_three s memory n bsize msize hcode hrun)
    (by simpa [entryState, Exp.bDone, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [entryState, Exp.bDone] using hfork)
    (by simpa [entryState, Exp.bDone] using hrun)
    (by simpa [entryState, Exp.bDone] using hnp)

def gasSteps_entry_other (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16) (hne : esize ≠ 3) (he : esize ≤ 1024)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (entryState s memory n bsize esize msize) rho)
      (append (otherWidth s memory n bsize esize msize) rho) :=
  CycleSubmission.Global.StackTail.gasSteps CycleSubmission.Global.FixedDirectPaths.entryPrefix rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_entry_other s memory n bsize esize msize hne he hcode hrun)
    (by simpa [entryState, Exp.bDone, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [entryState, Exp.bDone] using hfork)
    (by simpa [entryState, Exp.bDone] using hrun)
    (by simpa [entryState, Exp.bDone] using hnp)

def gasSteps_oneWidth_miss (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (otherWidth s memory n bsize esize msize) rho)
      (append (FixedDirectStates.bailState s memory n bsize esize msize) rho) :=
  CycleSubmission.Global.StackTail.gasSteps CycleSubmission.Global.FixedDirectPaths.oneWidth rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_oneWidth_miss s memory n bsize esize msize hcode hrun)
    (by simpa [otherWidth, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [otherWidth] using hfork)
    (by simpa [otherWidth] using hrun)
    (by simpa [otherWidth] using hnp)

def gasSteps_threeHit (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (FixedDirectStates.e3go s memory n bsize esize msize) rho)
      (append (FixedDirectStates.special s memory n bsize esize msize 1) rho) :=
  CycleSubmission.Global.StackTail.gasSteps CycleSubmission.Global.FixedDirectPaths.threeHit rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_threeHit s memory n bsize esize msize hcode hrun)
    (by simpa [FixedDirectStates.e3go, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [FixedDirectStates.e3go] using hfork)
    (by simpa [FixedDirectStates.e3go] using hrun)
    (by simpa [FixedDirectStates.e3go] using hnp)

def gasSteps_check65537_hit (s : State) (memory input : ByteArray)
    (n bsize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16) (hb : bsize ≤ 1024)
    (hvalue : exponentValue input bsize 3 = 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 88 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2656 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (FixedDirectStates.check65537 s memory n bsize 3 msize) rho)
      (append (FixedDirectStates.special s memory n bsize 3 msize 16) rho) :=
  CycleSubmission.Global.StackTail.gasSteps (CycleSubmission.Global.FixedDirectPaths.check65537 ++ CycleSubmission.Global.FixedDirectPaths.fermatHit) rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_check65537_hit s memory input n bsize msize hb hvalue hdata hactive
      heoff hrun)
    (by simpa [FixedDirectStates.check65537, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [FixedDirectStates.check65537] using hfork)
    (by simpa [FixedDirectStates.check65537] using hrun)
    (by simpa [FixedDirectStates.check65537] using hnp)

def gasSteps_check65537_miss (s : State) (memory input : ByteArray)
    (n bsize msize : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16) (hb : bsize ≤ 1024)
    (hvalue : exponentValue input bsize 3 ≠ 65537)
    (hdata : s.executionEnv.calldata = input)
    (hactive : 88 ≤ s.activeWords.toNat)
    (heoff : MachineState.readWord memory 2656 = UInt256.ofNat (96 + bsize))
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (append (FixedDirectStates.check65537 s memory n bsize 3 msize) rho)
      (append (FixedDirectStates.bailState s memory n bsize 3 msize) rho) :=
  CycleSubmission.Global.StackTail.gasSteps CycleSubmission.Global.FixedDirectPaths.check65537 rho
    (by simp [FixedExponentRoute.entryState, Exp.bDone, FixedDirectStates.otherWidth,
      FixedDirectStates.check65537, FixedDirectStates.e3go, FixedDirectStates.bailState,
      FixedDirectStates.special, Exp.outer, CycleSubmission.Global.FixedDirectPaths.entryPrefix,
      CycleSubmission.Global.FixedDirectPaths.oneWidth, CycleSubmission.Global.FixedDirectPaths.threeHit, CycleSubmission.Global.FixedDirectPaths.check65537,
      CycleSubmission.Global.FixedDirectPaths.fermatHit]; omega)
    (run_check65537_miss s memory input n bsize msize hb hvalue hdata hactive
      heoff hcode hrun)
    (by simpa [FixedDirectStates.check65537, CycleSubmission.Artifact.artifact] using hcode)
    (by simpa [FixedDirectStates.check65537] using hfork)
    (by simpa [FixedDirectStates.check65537] using hrun)
    (by simpa [FixedDirectStates.check65537] using hnp)

#print axioms gasSteps_entry_three
#print axioms gasSteps_entry_other
#print axioms gasSteps_oneWidth_miss
#print axioms gasSteps_threeHit
#print axioms gasSteps_check65537_hit
#print axioms gasSteps_check65537_miss

end CycleSubmission.Global.TailPrefix

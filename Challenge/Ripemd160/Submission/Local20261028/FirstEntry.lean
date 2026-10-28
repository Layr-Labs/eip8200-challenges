import Challenge.Ripemd160.Submission.Local20261028.RawDispatch
import Challenge.Ripemd160.Submission.Local20261028.ControlSites
import Challenge.Ripemd160.Submission.Local20261028.FirstMessageSpec
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstEntry
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate ControlSites
structure Env (s : State) : Prop where
  code : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode
  fork : s.fork = .Osaka
  running : s.halt = .Running
  noPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false

def high (s : State) : State :=
  {s with memory := PairedScheduleMemory.writeWord s.memory 162 FirstInitial.highWord}

theorem run_special (s : State) (rho : List UInt256) (hs : rho.length ≤ 880)
    (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hv : Decode.isValidJumpDest s.executionEnv.code 10108 = true) :
    runInstrSeq specialTemplate {s with pc := UInt256.ofNat 143, stack := FirstCore.frame (UInt256.ofNat 32) rho} =
      some {high s with pc := UInt256.ofNat 10108, stack := FirstCore.frame (UInt256.ofNat 9949) rho} := by
  have hcap (n : Nat) (hn : n ≤ 24) : rho.length+n < 1024 := by omega
  have hactive : s.activeWordsAfterUInt256 162 32 = s.activeWords :=
    Stagger144Active.word_active_preserved_of_small s.activeWords 162 ha (by decide)
  have hat : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 162 32) = s.activeWords := hactive
  have heq : ((UInt256.ofNat 32).eq (UInt256.ofNat 32)).isTrue = true := by decide
  simp (discharger := omega) [specialTemplate, runInstrSeq, DataStepper.runInstr,
    FirstCore.frame, StaggerPersistentFrame.frame, NormalPrepare.masks,
    high, PairedScheduleMemory.writeWord, FirstInitial.highWord,
    List.exchange, List.getElem?_cons_zero, hr, hcap, Nat.add_assoc, hactive, hv, heq, State.activeWordsAfterUInt256, hat]

def special (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 880)
    (ha : 34 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 143, stack := FirstCore.frame (UInt256.ofNat 32) rho}
      {high s with pc := UInt256.ofNat 10108, stack := FirstCore.frame (UInt256.ofNat 9949) rho} := by
  apply PadLift.gasSteps_of_raw specialSite {s with pc := UInt256.ofNat 143, stack := FirstCore.frame (UInt256.ofNat 32) rho}
    {high s with pc := UInt256.ofNat 10108, stack := FirstCore.frame (UInt256.ofNat 9949) rho}
    e.code e.fork e.running e.noPrecompile special_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact run_special s rho hs e.running ha (by rw [e.code]; exact valid10108)

def align (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 900)
    (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps {s with pc := UInt256.ofNat 447, stack := rho}
      {s with pc := UInt256.ofNat 143, stack := rho} := by
  apply PadLift.gasSteps_of_raw alignSite {s with pc := UInt256.ofNat 447, stack := rho}
    {s with pc := UInt256.ofNat 143, stack := rho}
    e.code e.fork e.running e.noPrecompile align_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · have hcap (n : Nat) (hn : n ≤ 24) : rho.length+n < 1024 := by omega
    have hv : Decode.isValidJumpDest s.executionEnv.code 143 = true := by rw [e.code]; exact valid143
    have ht : ((UInt256.ofNat 32).land (UInt256.ofNat 18446744073709551423)).isTrue = true := by decide
    simp [alignTemplate, runInstrSeq, DataStepper.runInstr, e.running, h32, hv, ht, hcap,
      show rho.length < 1024 by omega, show rho.length+1 < 1024 by omega,
      show rho.length+2 < 1024 by omega]

def dispatch (s : State) (e : Env s) (h : Compression.HashState) (off junk : UInt256)
    (rho : List UInt256) (hs : rho.length ≤ 980) :
    GasSteps {s with pc := UInt256.ofNat 4578, stack := junk :: StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho}
      {s with pc := UInt256.ofNat 9949, stack := StaggerPersistentFrame.frame h off junk rho} := by
  apply PadLift.gasSteps_of_raw dispatchSite {s with pc := UInt256.ofNat 4578, stack := junk :: StaggerPersistentFrame.frame h off (UInt256.ofNat 9949) rho}
    {s with pc := UInt256.ofNat 9949, stack := StaggerPersistentFrame.frame h off junk rho}
    e.code e.fork e.running e.noPrecompile dispatch_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact RawDispatch.run_dispatch s (UInt256.ofNat 4578) h off (UInt256.ofNat 9949) junk rho
      (by omega) e.running (by rw [e.code]; exact valid9949)
#print axioms run_special
#print axioms special
#print axioms align
#print axioms dispatch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstEntry

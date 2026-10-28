import Challenge.Ripemd160.Submission.Local20261028.FirstEntry
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstCopy
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate ControlSites FirstEntry

def copied (s : State) (input : ByteArray) : State :=
  {s with memory := FirstSpec.copiedMemory input, activeWords := UInt256.ofNat 34}

theorem run_copy (s : State) (input : ByteArray) (rho : List UInt256)
    (hs : rho.length ≤ 880) (hr : s.halt = .Running)
    (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hm : MachineState.writeBytes s.memory input 1056 = FirstSpec.copiedMemory input)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1056 32) = UInt256.ofNat 34) :
    runInstrSeq copyTemplate {s with pc := UInt256.ofNat 245, stack := rho} =
      some {copied s input with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho} := by
  have hcap (n : Nat) (hn : n ≤ 24) : rho.length+n < 1024 := by omega
  have hh : MachineState.readPadded input 0 32 = input := by
    rw [← h32, Memory.readPadded_zero_size]
  simp (discharger := omega) [copyTemplate, runInstrSeq, DataStepper.runInstr,
    copied, NormalPrepare.masks, hcal, h32, hm, ha, hr,
    hcap, hh, show rho.length < 1024 by omega, Nat.add_assoc, State.activeWordsAfterUInt256,
    show ({val := 0} : UInt256).toNat = 0 from rfl,
    DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
  all_goals repeat first | apply And.intro | rfl

def copy (s : State) (e : Env s) (input : ByteArray) (rho : List UInt256)
    (hs : rho.length ≤ 880) (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hm : MachineState.writeBytes s.memory input 1056 = FirstSpec.copiedMemory input)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1056 32) = UInt256.ofNat 34) :
    GasSteps {s with pc := UInt256.ofNat 245, stack := rho}
      {copied s input with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho} := by
  apply PadLift.gasSteps_of_raw copySite {s with pc := UInt256.ofNat 245, stack := rho}
    {copied s input with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho}
    e.code e.fork e.running e.noPrecompile copy_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact run_copy s input rho hs e.running hcal h32 hm ha

theorem run_frame (s : State) (rho : List UInt256) (hs : rho.length ≤ 880)
    (hr : s.halt = .Running) (h32 : s.executionEnv.calldata.size = 32) :
    runInstrSeq frameTemplate {s with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho} =
      some {s with pc := UInt256.ofNat 447, stack := FirstCore.frame (UInt256.ofNat 32) rho} := by
  have hcap (n : Nat) (hn : n ≤ 24) : rho.length+n < 1024 := by omega
  simp (discharger := omega) [frameTemplate, runInstrSeq, DataStepper.runInstr,
    FirstCore.frame, FirstCore.initialHash, StaggerPersistentFrame.frame,
    NormalPrepare.masks, hr, h32, hcap, Nat.add_assoc]
  all_goals repeat first | apply And.intro | rfl

def frame (s : State) (e : Env s) (rho : List UInt256) (hs : rho.length ≤ 880)
    (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps {s with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho}
      {s with pc := UInt256.ofNat 447, stack := FirstCore.frame (UInt256.ofNat 32) rho} := by
  apply PadLift.gasSteps_of_raw frameSite {s with pc := UInt256.ofNat 315, stack := NormalPrepare.masks rho}
    {s with pc := UInt256.ofNat 447, stack := FirstCore.frame (UInt256.ofNat 32) rho}
    e.code e.fork e.running e.noPrecompile frame_pc.symm
  · apply PadLift.advancesAll_sound; decide +kernel
  · exact run_frame s rho hs e.running h32

def entry (s : State) (e : Env s) (input : ByteArray) (rho : List UInt256)
    (hs : rho.length ≤ 880) (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hm : MachineState.writeBytes s.memory input 1056 = FirstSpec.copiedMemory input)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1056 32) = UInt256.ofNat 34) :
    GasSteps {s with pc := UInt256.ofNat 245, stack := rho}
      {high (copied s input) with pc := UInt256.ofNat 10108, stack := FirstCore.frame (UInt256.ofNat 9949) rho} := by
  have ec : Env (copied s input) := ⟨e.code,e.fork,e.running,e.noPrecompile⟩
  have hs32 : (copied s input).executionEnv.calldata.size = 32 := hcal ▸ h32
  have hf := frame (copied s input) ec rho hs hs32
  have ha' := align (copied s input) ec (FirstCore.frame (UInt256.ofNat 32) rho)
    (by simp [FirstCore.frame, StaggerPersistentFrame.frame, NormalPrepare.masks]; omega) hs32
  exact (copy s e input rho hs hcal h32 hm ha).trans
    (hf.trans (ha'.trans (special (copied s input) ec rho hs (by change (34 : Nat) ≤ 34; decide))))
#print axioms run_copy
#print axioms run_frame
#print axioms entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstCopy

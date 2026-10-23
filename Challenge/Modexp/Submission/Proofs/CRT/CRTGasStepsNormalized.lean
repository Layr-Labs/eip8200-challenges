import Challenge.Modexp.Submission.Proofs.CRT.CRTGasSteps
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopFrames
import Challenge.Modexp.Submission.Proofs.CRT.KernelRefinement
set_option warningAsError true
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace HistoricalSearch.CRTGasStepsNormalized
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open HistoricalSearch.GeneratedColumns HistoricalSearch.GeneratedArithmetic
open HistoricalSearch.ConcreteArithmetic HistoricalSearch.CRTAdapterMeaning
open HistoricalSearch.CRTLoopArithmetic HistoricalSearch.CRTLoopFrames

def entry (s : State) (mem : ByteArray) (f : CRTLoopFrames.Frame) (pbi ent : UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atOld s mem 4816 (UInt256.ofNat 0) pbi ent f)
      (atCache s (entryMemory mem f.counter) 5859 (inputWord mem 0)
        (MachineState.readWord mem 2720) f) := by
  have g := CRTGasSteps.gasSteps_entry {s with memory := mem} pbi (UInt256.ofNat 5297)
    f.w3 ent f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv
    (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (entry_normalize s mem f pbi ent)
#print axioms entry

/-- `entry` without the 4816 hook: the initial dispatch lands on 5615 directly. -/
def entryDirect (s : State) (mem : ByteArray) (f : CRTLoopFrames.Frame) (pbi ent : UInt256)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atOld s mem 5615 (UInt256.ofNat 0) pbi ent f)
      (atCache s (entryMemory mem f.counter) 5859 (inputWord mem 0)
        (MachineState.readWord mem 2720) f) := by
  have g := CRTGasSteps.gasSteps_entryDirect {s with memory := mem} pbi (UInt256.ofNat 5297)
    f.w3 ent f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv
    (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (entry_normalize s mem f pbi ent)
#print axioms entryDirect

def kernel (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat)
    (h0 : UInt256.land maskWord (MachineState.readWord mem 224) = n 0)
    (h8 : UInt256.shiftRight (MachineState.readWord mem 0) (UInt256.ofNat 160) = n 8) :
    GasSteps (atCache s mem 5859 n minv f)
      (atCache s (result {s with memory := mem} minv n []).memory 8129 n minv f) := by
  have hc : (saved f).length ≤ 998 := by rw [saved_length]; omega
  have g := CRTGasSteps.gasSteps_kernel {s with memory := mem} modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (saved f)
    (env.transfer rfl rfl) hc hact rfl h0 h8
  have he : kernelModel {s with memory := mem} modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (saved f) = afterKernel s mem n minv f :=
    KernelRefinement.model_eq_states _ _ _ _
  exact g.cast rfl (he.trans (afterKernel_normalize s mem n minv f))
#print axioms kernel

def overflow (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atCache s mem 8129 n minv f)
      (atCache s (checkedMemory mem)
        (if (UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 192)).toNat = 0 then 8145 else 8800) n minv f) := by
  have g := CRTGasSteps.gasSteps_overflow {s with memory := mem}
    modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (overflow_normalize s mem n minv f)
#print axioms overflow

def count (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atCache s mem 8145 n minv f)
      (atCache s mem (if (MachineState.readWord mem 1728).toNat = 0 then 8800 else 8154) n minv f) := by
  have g := CRTGasSteps.gasSteps_count {s with memory := mem}
    modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (count_normalize s mem n minv f)
#print axioms count

def retain (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atCache s mem 8154 n minv f)
      (atCache s (retainedMemory mem) 5859 n minv f) := by
  have g := CRTGasSteps.gasSteps_retain {s with memory := mem}
    modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (retain_normalize s mem n minv f)
#print axioms retain

def exit (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : CRTLoopFrames.Frame)
    (env : Environment Artifact.submissionArtifact .Osaka s)
    (hcap : f.rest.length ≤ 982) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (atCache s mem 8800 n minv f)
      (atOld s (exitMemory mem) 3942 (MachineState.readWord mem 1760)
        (UInt256.ofNat 0) (UInt256.ofNat 3643) (exitFrame mem f)) := by
  have g := CRTGasSteps.gasSteps_exit {s with memory := mem}
    modulusWord (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32 CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0) f.aprev f.counter f.ret f.rest (env.transfer rfl rfl) hcap hact
  exact g.cast rfl (exit_normalize s mem n minv f)
#print axioms exit

end HistoricalSearch.CRTGasStepsNormalized

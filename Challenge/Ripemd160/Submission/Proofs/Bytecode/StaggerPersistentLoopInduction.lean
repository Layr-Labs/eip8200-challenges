import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoopCompletionControl
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StaggerPersistentLoopRaw

structure Ambient (input : ByteArray) (s : State) : Prop where
  code : s.executionEnv.code = Artifact.submissionArtifact.code
  fork : s.fork = .Osaka
  running : s.halt = .Running
  notPrecompile : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  calldata : s.executionEnv.calldata = input

def limitWord (count : Nat) : UInt256 := UInt256.ofNat (count * 64)
def offsetWord (i : Nat) : UInt256 := UInt256.ofNat (i * 64)

def loopState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  {s with pc := LoopCompletionControl.blockPC input i, stack := StaggerPersistentFrame.frame h (offsetWord i) (LoopCompletionControl.limit input) rho}

def postState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4643, stack := StaggerPersistentFrame.frame h (offsetWord i) (LoopCompletionControl.limit input) rho}

def exitState (input : ByteArray) (s : State) (h : Compression.HashState) (count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4662, stack := StaggerPersistentFrame.frame h (limitWord count) (LoopCompletionControl.limit input) rho}

theorem next_offset (i count : Nat) (hi : i < count) (hbound : count * 64 < 2^256) :
    nextOffset (offsetWord i) = offsetWord (i + 1) := by
  change UInt256.ofNat (i * 64) + UInt256.ofNat 64 = UInt256.ofNat ((i + 1) * 64)
  rw [Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

def run_blocks (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState)
    (rho : List UInt256) (hsize : input.size < 2^64) (hstack : rho.length ≤ 880)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) rho)
        (postState input (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) rho)) :
    GasSteps (loopState input (states 0) (hashes 0) 0 (DriverTrace.blockCount input) rho)
      (exitState input (states (DriverTrace.blockCount input)) (hashes (DriverTrace.blockCount input))
        (DriverTrace.blockCount input) rho) := by
  let count := DriverTrace.blockCount input
  have hcount : 0 < count := DriverTrace.blockCount_pos input
  have hbound : count * 64 < 2^256 := LoopCompletionControl.padded_bound input hsize
  let I : Nat → State := fun i =>
    if i < count then loopState input (states i) (hashes i) i count rho
    else exitState input (states i) (hashes i) count rho
  have hb : ∀ i, i < count → GasSteps (I i) (I (i + 1)) := by
    intro i hi
    have a := hambient (i + 1) (by omega)
    have hfit : (states (i+1)).executionEnv.calldata.size < 2^256 := by
      rw [a.calldata]
      have : (2:Nat)^64 < 2^256 := by decide
      omega
    have ho : (nextOffset (offsetWord i)).toNat = (i+1)*64 := by
      rw [next_offset i count hi hbound]
      change ((i+1)*64) % 2^256 = (i+1)*64
      exact Nat.mod_eq_of_lt (by omega)
    have hl := LoopCompletionControl.limit_toNat input hsize
    by_cases hn : i + 1 < count
    · by_cases hh : input.size = (i+1)*64
      · have gp := StaggerPersistentLoopSites.gasSteps_pad (states (i+1)) (hashes (i+1))
          (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running
          (by rw [hl, ho]; exact LoopCompletionControl.pad_bound input i hh) hfit
          (by rw [a.calldata, ho]; exact hh) a.code a.fork a.notPrecompile
        rw [next_offset i count hi hbound] at gp
        have gb := hblock i hi
        simpa only [I, if_pos hi, if_pos hn, loopState, postState,
          LoopCompletionControl.blockPC, if_pos hh] using gb.trans gp
      · have gp := StaggerPersistentLoopSites.gasSteps_continue (states (i+1)) (hashes (i+1))
          (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running
          (by rw [hl, ho]; exact LoopCompletionControl.continue_lt input i hn hh)
          a.code a.fork a.notPrecompile
        rw [next_offset i count hi hbound] at gp
        have gb := hblock i hi
        simpa only [I, if_pos hi, if_pos hn, loopState, postState,
          LoopCompletionControl.blockPC, if_neg hh] using gb.trans gp
    · have he : i + 1 = count := by omega
      have gp := StaggerPersistentLoopSites.gasSteps_exit (states (i+1)) (hashes (i+1))
        (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running
        (by rw [hl, ho, he]; exact LoopCompletionControl.finish_bound input) hfit
        (by rw [a.calldata, ho, he]; exact LoopCompletionControl.finish_miss input)
        a.code a.fork a.notPrecompile
      rw [next_offset i count hi hbound, he] at gp
      have gb := hblock i hi
      rw [he] at gb
      simpa only [I, if_pos hi, if_neg hn, he, if_neg (Nat.lt_irrefl count), loopState,
        postState, exitState, offsetWord, limitWord] using gb.trans gp
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

#print axioms run_blocks
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction

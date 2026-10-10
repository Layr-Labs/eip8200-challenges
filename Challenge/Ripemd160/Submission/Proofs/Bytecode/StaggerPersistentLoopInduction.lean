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

def limitWord (count : Nat) : UInt256 := DriverTrace.messageOffsetWord count
/-- Block pointers are absolute: the calldata copy starts at memory 1056. -/
def offsetWord (i : Nat) : UInt256 := DriverTrace.messageOffsetWord i

def loopState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  {s with pc := LoopCompletionControl.blockPC input i, stack := entryStack input i h (offsetWord i) (LoopCompletionControl.limit input) rho}

def postState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4556, stack := StaggerPersistentFrame.frame h (blockMark input i (offsetWord i)) (LoopCompletionControl.limit input) rho}

def exitState (input : ByteArray) (s : State) (h : Compression.HashState) (count : Nat) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4581, stack := StaggerPersistentFrame.frame h (blockMark input (count - 1) (offsetWord (count - 1))) (LoopCompletionControl.limit input) rho}

theorem next_offset (i count : Nat) (hi : i < count) (hbound : 1056 + count * 64 < 2^256) :
    nextOffset (offsetWord i) = offsetWord (i + 1) := by
  change UInt256.ofNat (1056 + i * 64) + UInt256.ofNat 64 = UInt256.ofNat (1056 + (i + 1) * 64)
  rw [Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

def run_blocks (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState)
    (rho : List UInt256) (hsize : input.size < 2^64) (hstack : rho.length ≤ 880)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states i))
    (hmsize : ∀ i, i + 1 < DriverTrace.blockCount input →
      ((input.size = (i + 1) * 64 ∧ input.size < 256) →
        UInt256.ofNat (32 * (states (i + 1)).activeWords.toNat) = offsetWord (i + 1)) ∧
      (¬ (input.size = (i + 1) * 64 ∧ input.size < 256) →
        UInt256.ofNat (32 * (states (i + 1)).activeWords.toNat) ≠ offsetWord (i + 1)))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) rho)
        (postState input (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) rho)) :
    GasSteps (loopState input (states 0) (hashes 0) 0 (DriverTrace.blockCount input) rho)
      (exitState input (states (DriverTrace.blockCount input)) (hashes (DriverTrace.blockCount input))
        (DriverTrace.blockCount input) rho) := by
  let count := DriverTrace.blockCount input
  have hcount : 0 < count := DriverTrace.blockCount_pos input
  have hbound : 1056 + count * 64 < 2^256 := by
    rw [← DriverTrace.paddedLength_eq_blockCount]
    have h := Padding.paddedLength_lt input.size
    have h2 : (2:Nat)^64 + 2000 < 2^256 := by decide
    omega
  let I : Nat → State := fun i =>
    if i < count then loopState input (states i) (hashes i) i count rho
    else exitState input (states i) (hashes i) count rho
  have hb : ∀ i, i < count → GasSteps (I i) (I (i + 1)) := by
    intro i hi
    have a := hambient (i + 1) (by omega)
    have hoff : (offsetWord i).toNat = 1056 + i * 64 := by
      change (1056 + i * 64) % 2^256 = 1056 + i * 64
      exact Nat.mod_eq_of_lt (by omega)
    have ho : (nextOffset (offsetWord i)).toNat = 1056 + (i+1)*64 := by
      rw [next_offset i count hi hbound]
      change (1056 + (i+1)*64) % 2^256 = 1056 + (i+1)*64
      exact Nat.mod_eq_of_lt (by omega)
    have hl := LoopCompletionControl.limit_toNat input hsize
    have gb := hblock i hi
    by_cases hn : i + 1 < count
    · have hip : ¬ (input.size = i * 64 ∧ input.size < 256) := fun hh => by
        have := LoopCompletionControl.pad_last input i hh
        omega
      have hmark : blockMark input i (offsetWord i) = offsetWord i := by
        simp only [blockMark, if_neg hip]
      have hle : (offsetWord i).toNat ≤ (LoopCompletionControl.limit input).toNat := by
        rw [hoff, hl]
        exact LoopCompletionControl.not_finish input i hn
      by_cases hh : input.size = (i+1)*64 ∧ input.size < 256
      · have gp := StaggerPersistentLoopSites.gasSteps_pad (states (i+1)) (hashes (i+1))
          (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running hle
          (by
            rw [next_offset i count hi hbound]
            exact ((hmsize i hn).1 hh).symm)
          a.code a.fork a.notPrecompile
        rw [next_offset i count hi hbound] at gp
        simp only [postState, hmark] at gb
        simpa only [I, if_pos hi, if_pos hn, loopState, LoopCompletionControl.blockPC, entryStack,
          if_pos hh, if_neg hip] using gb.trans gp
      · have gp := StaggerPersistentLoopSites.gasSteps_continue (states (i+1)) (hashes (i+1))
          (offsetWord i) (LoopCompletionControl.limit input) rho (by omega) a.running hle
          (by
            rw [next_offset i count hi hbound]
            exact fun heq => (hmsize i hn).2 hh heq.symm)
          a.code a.fork a.notPrecompile
        rw [next_offset i count hi hbound] at gp
        simp only [postState, hmark] at gb
        simpa only [I, if_pos hi, if_pos hn, loopState, LoopCompletionControl.blockPC, entryStack,
          if_neg hh, if_neg hip] using gb.trans gp
    · have he : i + 1 = count := by omega
      have hi1 : count - 1 = i := by omega
      have hgt : (LoopCompletionControl.limit input).toNat < (blockMark input i (offsetWord i)).toNat := by
        rw [hl]
        by_cases hp : input.size = i * 64 ∧ input.size < 256
        · simp only [blockMark, if_pos hp, padMark_toNat]
          have hmod : input.size % 64 = 0 := by omega
          unfold LoopCompletionControl.limitNat
          rw [if_pos ⟨hmod, hp.2⟩]
          omega
        · simp only [blockMark, if_neg hp, hoff]
          have hc := LoopCompletionControl.finish_cold input (by
            change ¬ (input.size = (count - 1) * 64 ∧ input.size < 256)
            rw [hi1]; exact hp)
          change LoopCompletionControl.limitNat input < 1056 + (count - 1) * 64 at hc
          rw [hi1] at hc
          exact hc
      have gp := StaggerPersistentLoopSites.gasSteps_exit (states (i+1)) (hashes (i+1))
        (blockMark input i (offsetWord i)) (LoopCompletionControl.limit input) rho (by omega) a.running
        hgt a.code a.fork a.notPrecompile
      rw [he] at gb gp
      simpa only [I, if_pos hi, if_neg hn, he, if_neg (Nat.lt_irrefl count), loopState,
        postState, exitState, hi1] using gb.trans gp
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction

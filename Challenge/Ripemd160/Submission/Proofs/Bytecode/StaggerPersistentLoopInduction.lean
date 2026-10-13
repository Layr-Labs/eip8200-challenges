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

/-- Block pointers are absolute: the calldata copy starts at memory 1056. -/
def offsetWord (i : Nat) : UInt256 := DriverTrace.messageOffsetWord i

/-- The active memory size `MSIZE` reads. -/
def msize (s : State) : UInt256 := UInt256.ofNat (32 * s.activeWords.toNat)

def loopState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := LoopCompletionControl.blockPC input i
    stack := entryStack input i h (offsetWord i) (LoopCompletionControl.cont input) rho }

def postState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4551
    stack := StaggerPersistentFrame.frame h (blockMark input i (offsetWord i) (LoopCompletionControl.cont input))
      (blockCont input i (LoopCompletionControl.cont input)) rho }

def exitState (input : ByteArray) (s : State) (h : Compression.HashState) (count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat outPC
    stack := StaggerPersistentFrame.frame h (blockMark input (count - 1) (offsetWord (count - 1))
      (LoopCompletionControl.cont input)) (blockCont input (count - 1) (LoopCompletionControl.cont input)) rho }

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
        msize (states (i + 1)) = offsetWord (i + 1)) ∧
      (¬ (input.size = (i + 1) * 64 ∧ input.size < 256) →
        msize (states (i + 1)) ≠ offsetWord (i + 1)))
    (hlast : ¬ (input.size % 64 = 0 ∧ input.size < 256) → ∀ i, i < DriverTrace.blockCount input →
      ((msize (states (i + 1))).toNat < (offsetWord i + UInt256.ofNat 128).toNat ↔
        i + 1 = DriverTrace.blockCount input))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) rho)
        (postState input (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) rho)) :
    GasSteps (loopState input (states 0) (hashes 0) 0 (DriverTrace.blockCount input) rho)
      (exitState input (states (DriverTrace.blockCount input)) (hashes (DriverTrace.blockCount input))
        (DriverTrace.blockCount input) rho) := by
  let count := DriverTrace.blockCount input
  let c := LoopCompletionControl.cont input
  have hcdef : LoopCompletionControl.cont input = c := rfl
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
    have gb := hblock i hi
    by_cases hal : input.size % 64 = 0 ∧ input.size < 256
    · have hc : c = UInt256.ofNat 4768 := LoopCompletionControl.cont_aligned input hal
      by_cases hp : input.size = i * 64 ∧ input.size < 256
      · -- the pad-only block: its continuation is the output entry
        have he : i + 1 = count := LoopCompletionControl.pad_last input i hp
        have hi1 : count - 1 = i := by omega
        have gd := StaggerPersistentLoopSites.gasSteps_dispatch (states (i + 1)) (hashes (i + 1))
          (blockMark input i (offsetWord i) c) (blockCont input i c) rho (by omega) a.running
          (by
            simp only [blockCont, if_pos hp]
            exact StaggerPersistentLoopSites.valid_out (states (i + 1)) a.code)
          a.code a.fork a.notPrecompile
        rw [he] at gb gd
        have gx := gb.trans gd
        simpa only [I, if_pos hi, if_neg (Nat.lt_irrefl count), he, loopState, postState, exitState,
          hi1, blockCont, if_pos hp] using gx
      · have hn : i + 1 < count := by
          by_contra hn
          exact hp (LoopCompletionControl.aligned_last input hal i (by omega))
        have hmark : blockMark input i (offsetWord i) c = offsetWord i := by
          simp only [blockMark, if_neg hp]
        have hcont : blockCont input i c = c := by
          simp only [blockCont, if_neg hp]
        have gd := StaggerPersistentLoopSites.gasSteps_dispatch (states (i + 1)) (hashes (i + 1))
          (offsetWord i) c rho (by omega) a.running
          (by rw [hc]; exact StaggerPersistentLoopSites.valid_chain (states (i + 1)) a.code)
          a.code a.fork a.notPrecompile
        rw [hc] at gd
        by_cases hh : input.size = (i + 1) * 64 ∧ input.size < 256
        · have gp := StaggerPersistentLoopSites.gasSteps_pad (states (i + 1)) (hashes (i + 1))
            (offsetWord i) (UInt256.ofNat 4768) rho (by omega) a.running
            (by
              rw [next_offset i count hi hbound]
              exact ((hmsize i hn).1 hh).symm)
            a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at gp
          simp only [postState, hcdef] at gb; rw [hmark, hcont, hc] at gb
          simpa only [I, if_pos hi, if_pos hn, loopState, LoopCompletionControl.blockPC, entryStack,
            if_pos hh, hcdef, hc] using gb.trans (gd.trans gp)
        · have gp := StaggerPersistentLoopSites.gasSteps_continue (states (i + 1)) (hashes (i + 1))
            (offsetWord i) (UInt256.ofNat 4768) rho (by omega) a.running
            (by
              rw [next_offset i count hi hbound]
              exact fun heq => (hmsize i hn).2 hh heq.symm)
            a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at gp
          simp only [postState, hcdef] at gb; rw [hmark, hcont, hc] at gb
          simpa only [I, if_pos hi, if_pos hn, loopState, LoopCompletionControl.blockPC, entryStack,
            if_neg hh, hcdef, hc] using gb.trans (gd.trans gp)
    · have hc : c = UInt256.ofNat 4757 := LoopCompletionControl.cont_cold input hal
      have hp := LoopCompletionControl.cold_not_pad input hal i
      have hmark : blockMark input i (offsetWord i) c = offsetWord i := by
        simp only [blockMark, if_neg hp]
      have hcont : blockCont input i c = c := by
        simp only [blockCont, if_neg hp]
      have gd := StaggerPersistentLoopSites.gasSteps_dispatch (states (i + 1)) (hashes (i + 1))
        (offsetWord i) c rho (by omega) a.running
        (by rw [hc]; exact StaggerPersistentLoopSites.valid_gl (states (i + 1)) a.code)
        a.code a.fork a.notPrecompile
      rw [hc] at gd
      simp only [postState, hcdef] at gb; rw [hmark, hcont, hc] at gb
      have hl := hlast hal i hi
      by_cases hn : i + 1 < count
      · have hge : ¬ (msize (states (i + 1))).toNat < (offsetWord i + UInt256.ofNat 128).toNat :=
          fun h => by have := hl.mp h; omega
        have gs := StaggerPersistentLoopSites.gasSteps_glStay (states (i + 1)) (hashes (i + 1))
          (offsetWord i) (UInt256.ofNat 4757) rho (by omega) a.running hge a.code a.fork a.notPrecompile
        have hh := LoopCompletionControl.cold_not_pad input hal (i + 1)
        have gp := StaggerPersistentLoopSites.gasSteps_continue (states (i + 1)) (hashes (i + 1))
          (offsetWord i) (UInt256.ofNat 4757) rho (by omega) a.running
          (by
            rw [next_offset i count hi hbound]
            exact fun heq => (hmsize i hn).2 hh heq.symm)
          a.code a.fork a.notPrecompile
        rw [next_offset i count hi hbound] at gp
        simpa only [I, if_pos hi, if_pos hn, loopState, LoopCompletionControl.blockPC, entryStack,
          if_neg hh, hcdef, hc] using gb.trans (gd.trans (gs.trans gp))
      · have he : i + 1 = count := by omega
        have hi1 : count - 1 = i := by omega
        have hlt : (msize (states (i + 1))).toNat < (offsetWord i + UInt256.ofNat 128).toNat := hl.mpr he
        have gx := StaggerPersistentLoopSites.gasSteps_glExit (states (i + 1)) (hashes (i + 1))
          (offsetWord i) (UInt256.ofNat 4757) rho (by omega) a.running hlt a.code a.fork a.notPrecompile
        rw [he] at gb gd gx
        simpa only [I, if_pos hi, if_neg (Nat.lt_irrefl count), he, loopState, exitState, hi1,
          blockMark, blockCont, if_neg hp, hcdef, hc] using gb.trans (gd.trans gx)
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction

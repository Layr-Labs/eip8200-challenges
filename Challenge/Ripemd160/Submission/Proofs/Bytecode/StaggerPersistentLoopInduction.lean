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

/-- The slot-11 offset while block `i` runs. -/
def blockOff (input : ByteArray) (i : Nat) : UInt256 :=
  offsetWord (LoopCompletionControl.offIndex input i)

def loopState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := LoopCompletionControl.blockPC input i
    stack := StaggerPersistentFrame.frame h (blockOff input i) (LoopCompletionControl.cont input i) rho }

def postState (input : ByteArray) (s : State) (h : Compression.HashState) (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4551
    stack := StaggerPersistentFrame.frame h (blockOff input i)
      (blockCont input i (LoopCompletionControl.cont input i)) rho }

def exitState (input : ByteArray) (s : State) (h : Compression.HashState) (count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat outPC
    stack := StaggerPersistentFrame.frame h (blockOff input (count - 1))
      (blockCont input (count - 1) (LoopCompletionControl.cont input (count - 1))) rho }

theorem next_offset (i count : Nat) (hi : i < count) (hbound : 1056 + count * 64 < 2^256) :
    nextOffset (offsetWord i) = offsetWord (i + 1) := by
  change UInt256.ofNat (1056 + i * 64) + UInt256.ofNat 64 = UInt256.ofNat (1056 + (i + 1) * 64)
  rw [Word.ofNat_add_ofNat (by omega)]
  congr 1
  omega

private theorem blockOff_msg (input : ByteArray) (i : Nat)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) : blockOff input i = offsetWord i := by
  simp only [blockOff, LoopCompletionControl.offIndex, if_neg hp]

private theorem blockPC_msg (input : ByteArray) (i : Nat)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) :
    LoopCompletionControl.blockPC input i = UInt256.ofNat 458 := by
  simp only [LoopCompletionControl.blockPC, if_neg hp]

private theorem blockCont_msg (input : ByteArray) (i : Nat) (c : UInt256)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) : blockCont input i c = c := by
  simp only [blockCont, if_neg hp]

private theorem blockCont_pad (input : ByteArray) (i : Nat) (c : UInt256)
    (hp : input.size = i * 64 ∧ input.size < 256) : blockCont input i c = UInt256.ofNat outPC := by
  simp only [blockCont, if_pos hp]

def run_blocks (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState)
    (rho : List UInt256) (hsize : input.size < 2^64) (hstack : rho.length ≤ 880)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states i))
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
    let s' := states (i + 1)
    let h' := hashes (i + 1)
    by_cases hp : input.size = i * 64 ∧ input.size < 256
    · -- the pad-only block: its continuation is the output entry
      have he : i + 1 = count := LoopCompletionControl.pad_last input i hp
      have hi1 : count - 1 = i := by omega
      have gd := StaggerPersistentLoopSites.gasSteps_dispatch s' h'
        (blockOff input i) (blockCont input i (LoopCompletionControl.cont input i)) rho (by omega) a.running
        (by rw [blockCont_pad input i _ hp]; exact StaggerPersistentLoopSites.valid_out s' a.code)
        a.code a.fork a.notPrecompile
      rw [blockCont_pad input i _ hp] at gd
      have hpost : postState input s' h' i count rho =
          { s' with
            pc := UInt256.ofNat 4551
            stack := StaggerPersistentFrame.frame h' (blockOff input i) (UInt256.ofNat outPC) rho } := by
        simp only [postState, blockCont_pad input i _ hp]
      have hexit : exitState input s' h' count rho =
          { s' with
            pc := UInt256.ofNat outPC
            stack := StaggerPersistentFrame.frame h' (blockOff input i) (UInt256.ofNat outPC) rho } := by
        simp only [exitState, hi1, blockCont_pad input i _ hp]
      have hI1 : I (i + 1) = exitState input s' h' count rho := by
        simp only [I, s', h', show ¬ (i + 1 < count) by omega, if_false]
      have hI0 : I i = loopState input (states i) (hashes i) i count rho := by simp only [I, if_pos hi]
      rw [hpost] at gb
      rw [hI0, hI1, hexit]
      exact gb.trans gd
    · have hoff := blockOff_msg input i hp
      have hcm := blockCont_msg input i (LoopCompletionControl.cont input i) hp
      rw [show I i = loopState input (states i) (hashes i) i count rho by simp only [I, if_pos hi]]
      simp only [postState, hoff, hcm] at gb
      by_cases hal : input.size % 64 = 0 ∧ input.size < 256
      · have hc := LoopCompletionControl.cont_aligned input hal i hp
        have hcases := LoopCompletionControl.aligned_cases input hal i hp hi
        if h192 : input.size - 64 * i = 192 then
          have hn : ¬ (input.size = (i + 1) * 64 ∧ input.size < 256) := fun h => by omega
          have hn1 : i + 1 < count := by
            unfold count DriverTrace.blockCount Padding.paddedLength at hi ⊢
            omega
          rw [hc, h192] at gb
          have gd := StaggerPersistentLoopSites.gasSteps_dispatch s' h' (offsetWord i) (UInt256.ofNat 192)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_stub192 s' a.code) a.code a.fork a.notPrecompile
          have gs := StaggerPersistentLoopSites.gasSteps_stub192 s' h' (offsetWord i) (UInt256.ofNat 192)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          have ga := StaggerPersistentLoopSites.gasSteps_advance s' h' (offsetWord i) (UInt256.ofNat 128)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at ga
          have hc1 : LoopCompletionControl.cont input (i + 1) = UInt256.ofNat 128 := by
            rw [LoopCompletionControl.cont_aligned input hal (i + 1) hn]; congr 1; omega
          simpa only [I, if_pos hn1, loopState, blockPC_msg input (i + 1) hn, blockOff_msg input (i + 1) hn, hc1]
            using gb.trans (gd.trans (gs.trans ga))
        else if h128 : input.size - 64 * i = 128 then
          have hn : ¬ (input.size = (i + 1) * 64 ∧ input.size < 256) := fun h => by omega
          have hn1 : i + 1 < count := by
            unfold count DriverTrace.blockCount Padding.paddedLength at hi ⊢
            omega
          rw [hc, h128] at gb
          have gd := StaggerPersistentLoopSites.gasSteps_dispatch s' h' (offsetWord i) (UInt256.ofNat 128)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_stub128 s' a.code) a.code a.fork a.notPrecompile
          have gs := StaggerPersistentLoopSites.gasSteps_stub128 s' h' (offsetWord i) (UInt256.ofNat 128)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          have ga := StaggerPersistentLoopSites.gasSteps_advance s' h' (offsetWord i) (UInt256.ofNat 64)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at ga
          have hc1 : LoopCompletionControl.cont input (i + 1) = UInt256.ofNat 64 := by
            rw [LoopCompletionControl.cont_aligned input hal (i + 1) hn]; congr 1; omega
          simpa only [I, if_pos hn1, loopState, blockPC_msg input (i + 1) hn, blockOff_msg input (i + 1) hn, hc1]
            using gb.trans (gd.trans (gs.trans ga))
        else
          have h64 : input.size - 64 * i = 64 := by omega
          have hn : input.size = (i + 1) * 64 ∧ input.size < 256 := by omega
          have hn1 : i + 1 < count := by
            have := LoopCompletionControl.pad_last input (i + 1) hn
            omega
          rw [hc, h64] at gb
          have gd := StaggerPersistentLoopSites.gasSteps_dispatch s' h' (offsetWord i) (UInt256.ofNat 64)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_pad s' a.code) a.code a.fork a.notPrecompile
          have hpc1 : LoopCompletionControl.blockPC input (i + 1) = UInt256.ofNat 64 := by
            simp only [LoopCompletionControl.blockPC, if_pos hn]
          have hoff1 : blockOff input (i + 1) = offsetWord i := by
            simp only [blockOff, LoopCompletionControl.offIndex, if_pos hn, Nat.add_sub_cancel]
          have hc1 : LoopCompletionControl.cont input (i + 1) = UInt256.ofNat 64 :=
            LoopCompletionControl.cont_pad input (i + 1) hn
          simpa only [I, if_pos hn1, loopState, hpc1, hoff1, hc1] using gb.trans gd
      · have hc := LoopCompletionControl.cont_cold input hal i
        rw [hc] at gb
        have gd := StaggerPersistentLoopSites.gasSteps_dispatch s' h' (offsetWord i) (UInt256.ofNat 47)
          rho (by omega) a.running (StaggerPersistentLoopSites.valid_gl s' a.code) a.code a.fork a.notPrecompile
        have hl := hlast hal i hi
        by_cases hn : i + 1 < count
        · have hge : ¬ (msize s').toNat < (offsetWord i + UInt256.ofNat 128).toNat :=
            fun h => by have := hl.mp h; omega
          have gs := StaggerPersistentLoopSites.gasSteps_glStay s' h' (offsetWord i) (UInt256.ofNat 47)
            rho (by omega) a.running hge a.code a.fork a.notPrecompile
          have ga := StaggerPersistentLoopSites.gasSteps_advance s' h' (offsetWord i) (UInt256.ofNat 47)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at ga
          have hp1 := LoopCompletionControl.cold_not_pad input hal (i + 1)
          simpa only [I, if_pos hn, loopState, blockPC_msg input (i + 1) hp1, blockOff_msg input (i + 1) hp1,
            LoopCompletionControl.cont_cold input hal (i + 1)] using gb.trans (gd.trans (gs.trans ga))
        · have he : i + 1 = count := by omega
          have hi1 : count - 1 = i := by omega
          have hlt : (msize s').toNat < (offsetWord i + UInt256.ofNat 128).toNat := hl.mpr he
          have gx := StaggerPersistentLoopSites.gasSteps_glExit s' h' (offsetWord i) (UInt256.ofNat 47)
            rho (by omega) a.running hlt a.code a.fork a.notPrecompile
          have hI1 : I (i + 1) = exitState input s' h' count rho := by
            simp only [I, s', h', show ¬ (i + 1 < count) by omega, if_false]
          rw [hI1]
          simpa only [exitState, s', h', count, hi1, hoff, blockCont_msg input i _ hp, hc] using gb.trans (gd.trans gx)
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction

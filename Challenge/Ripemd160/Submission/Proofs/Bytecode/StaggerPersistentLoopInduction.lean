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

/-- The pad-only block's frame is completed by the tail copy at its target 64, so its
continuation slot holds 64; every other block holds its scheduled continuation. -/
def loopCont (input : ByteArray) (_previous : Compression.HashState) (i : Nat) : UInt256 :=
  if input.size = i * 64 ∧ input.size < 256 then UInt256.ofNat 64
  else LoopCompletionControl.cont input i

theorem loopCont_pad (input : ByteArray) (previous : Compression.HashState) (i : Nat)
    (hp : input.size = i * 64 ∧ input.size < 256) :
    loopCont input previous i = UInt256.ofNat 64 := by
  simp only [loopCont, if_pos hp]

theorem loopCont_msg (input : ByteArray) (previous : Compression.HashState) (i : Nat)
    (hp : ¬ (input.size = i * 64 ∧ input.size < 256)) :
    loopCont input previous i = LoopCompletionControl.cont input i := by
  simp only [loopCont, if_neg hp]

@[simp] theorem blockCont_loopCont (input : ByteArray) (previous : Compression.HashState) (i : Nat) :
    blockCont input i (loopCont input previous i) =
      blockCont input i (LoopCompletionControl.cont input i) := by
  unfold loopCont blockCont
  split <;> rfl

def loopState (input : ByteArray) (s : State) (previous h : Compression.HashState)
    (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := LoopCompletionControl.blockPC input i
    stack := StaggerPersistentFrame.frame h (blockOff input i) (loopCont input previous i) rho }

/-- Block exit (4537): the resident tail stopped before its last eight instructions; the old hash
`oldh` and the block's memory determine the stack, which completes to `result s.memory oldh`. -/
def postState (input : ByteArray) (s : State) (oldh _h : Compression.HashState)
    (i _count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4537
    stack := PersistentStaggerTailBridge.preStack s.memory oldh (blockOff input i)
      (blockCont input i (LoopCompletionControl.cont input i)) rho }

/-- Serializer entry: the last block's exit stack at the output entry 4733. -/
def exitState (input : ByteArray) (s : State) (previous _h : Compression.HashState)
    (count : Nat) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat outPC
    stack := PersistentStaggerTailBridge.preStack s.memory previous (blockOff input (count - 1))
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
    LoopCompletionControl.blockPC input i = UInt256.ofNat 461 := by
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
    (hhash : ∀ i, i < DriverTrace.blockCount input →
      hashes (i + 1) = PersistentStaggerFunctional.result (states (i + 1)).memory (hashes i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes (i - 1)) (hashes i) i (DriverTrace.blockCount input) rho)
        (postState input (states (i + 1)) (hashes i) (hashes (i + 1)) i (DriverTrace.blockCount input) rho)) :
    GasSteps (loopState input (states 0) (hashes 0) (hashes 0) 0 (DriverTrace.blockCount input) rho)
      (exitState input (states (DriverTrace.blockCount input)) (hashes (DriverTrace.blockCount input - 1)) (hashes (DriverTrace.blockCount input))
        (DriverTrace.blockCount input) rho) := by
  let count := DriverTrace.blockCount input
  have hcount : 0 < count := DriverTrace.blockCount_pos input
  have hbound : 1056 + count * 64 < 2^256 := by
    rw [← DriverTrace.paddedLength_eq_blockCount]
    have h := Padding.paddedLength_lt input.size
    have h2 : (2:Nat)^64 + 2000 < 2^256 := by decide
    omega
  let I : Nat → State := fun i =>
    if i < count then loopState input (states i) (hashes (i - 1)) (hashes i) i count rho
    else exitState input (states i) (hashes (count - 1)) (hashes i) count rho
  have hb : ∀ i, i < count → GasSteps (I i) (I (i + 1)) := by
    intro i hi
    have a := hambient (i + 1) (by omega)
    have gb := hblock i hi
    have hh := hhash i hi
    let s' := states (i + 1)
    let h' := hashes (i + 1)
    have hI0 : I i = loopState input (states i) (hashes (i - 1)) (hashes i) i count rho := by
      simp only [I, if_pos hi]
    rw [hI0]
    by_cases hp : input.size = i * 64 ∧ input.size < 256
    · -- The pad-only block installs outPC; the exit goes straight to the serializer.
      have he : i + 1 = count := LoopCompletionControl.pad_last input i hp
      have hi1 : count - 1 = i := by omega
      have gd := StaggerPersistentLoopSites.gasSteps_exit s' s'.memory (hashes i)
        (blockOff input i) (UInt256.ofNat outPC) rho (by omega) a.running
        (StaggerPersistentLoopSites.valid_out s' a.code) a.code a.fork a.notPrecompile
      have hpost : postState input s' (hashes i) h' i count rho =
          {s' with pc := UInt256.ofNat 4537, stack := PersistentStaggerTailBridge.preStack s'.memory (hashes i) (blockOff input i) (UInt256.ofNat outPC) rho} := by
        simp only [postState, blockCont_pad input i _ hp]
      have hexit : I (i + 1) =
          {s' with pc := UInt256.ofNat outPC, stack := PersistentStaggerTailBridge.preStack s'.memory (hashes i) (blockOff input i) (UInt256.ofNat outPC) rho} := by
        simp only [I, s', show ¬ (i + 1 < count) by omega, if_false, exitState, hi1, blockCont_pad input i _ hp]
      rw [hpost] at gb
      rw [hexit]
      exact gb.trans gd
    · have hoff := blockOff_msg input i hp
      have hcm := blockCont_msg input i (LoopCompletionControl.cont input i) hp
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
          have gd := StaggerPersistentLoopSites.gasSteps_exit s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 192)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_stub192 s' a.code) a.code a.fork a.notPrecompile
          have gs := StaggerPersistentLoopSites.gasSteps_stub192 s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 192)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at gs
          have hc1 : LoopCompletionControl.cont input (i + 1) = UInt256.ofNat 128 := by
            rw [LoopCompletionControl.cont_aligned input hal (i + 1) hn]; congr 1; omega
          simpa only [I, if_pos hn1, loopState, loopCont, if_neg hn, blockPC_msg input (i + 1) hn, blockOff_msg input (i + 1) hn, hc1,
            Nat.add_sub_cancel, hh, s', StaggerPersistentLoopSites.result]
            using gb.trans (gd.trans gs)
        else if h128 : input.size - 64 * i = 128 then
          have hn : ¬ (input.size = (i + 1) * 64 ∧ input.size < 256) := fun h => by omega
          have hn1 : i + 1 < count := by
            unfold count DriverTrace.blockCount Padding.paddedLength at hi ⊢
            omega
          rw [hc, h128] at gb
          have gd := StaggerPersistentLoopSites.gasSteps_exit s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 128)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_stub128 s' a.code) a.code a.fork a.notPrecompile
          have gs := StaggerPersistentLoopSites.gasSteps_stub128 s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 128)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at gs
          have hc1 : LoopCompletionControl.cont input (i + 1) = UInt256.ofNat 64 := by
            rw [LoopCompletionControl.cont_aligned input hal (i + 1) hn]; congr 1; omega
          simpa only [I, if_pos hn1, loopState, loopCont, if_neg hn, blockPC_msg input (i + 1) hn, blockOff_msg input (i + 1) hn, hc1,
            Nat.add_sub_cancel, hh, s', StaggerPersistentLoopSites.result]
            using gb.trans (gd.trans gs)
        else
          have h64 : input.size - 64 * i = 64 := by omega
          have hn : input.size = (i + 1) * 64 ∧ input.size < 256 := by omega
          have hn1 : i + 1 < count := by
            have := LoopCompletionControl.pad_last input (i + 1) hn
            omega
          rw [hc, h64] at gb
          have gd := StaggerPersistentLoopSites.gasSteps_exit s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 64)
            rho (by omega) a.running (StaggerPersistentEntrySites.valid_pad s' a.code) a.code a.fork a.notPrecompile
          have gs := StaggerPersistentLoopSites.gasSteps_padEntry s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 64)
            rho (by omega) a.running a.code a.fork a.notPrecompile
          have hpc1 : LoopCompletionControl.blockPC input (i + 1) = UInt256.ofNat 74 := by
            simp only [LoopCompletionControl.blockPC, if_pos hn]
          have hoff1 : blockOff input (i + 1) = offsetWord i := by
            simp only [blockOff, LoopCompletionControl.offIndex, if_pos hn, Nat.add_sub_cancel]
          simpa only [I, if_pos hn1, loopState, loopCont, if_pos hn, hpc1, hoff1,
            Nat.add_sub_cancel, hh, s', StaggerPersistentLoopSites.result] using gb.trans (gd.trans gs)
      · have hc := LoopCompletionControl.cont_cold input hal i
        rw [hc] at gb
        have gd := StaggerPersistentLoopSites.gasSteps_exit s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 48)
          rho (by omega) a.running (StaggerPersistentLoopSites.valid_gl s' a.code) a.code a.fork a.notPrecompile
        have hl := hlast hal i hi
        by_cases hn : i + 1 < count
        · have hge : ¬ (msize s').toNat < (offsetWord i + UInt256.ofNat 128).toNat :=
            fun h => by have := hl.mp h; omega
          have gs := StaggerPersistentLoopSites.gasSteps_glStay s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 48)
            rho (by omega) a.running hge a.code a.fork a.notPrecompile
          rw [next_offset i count hi hbound] at gs
          have hp1 := LoopCompletionControl.cold_not_pad input hal (i + 1)
          simpa only [I, if_pos hn, loopState, loopCont, if_neg hp1, blockPC_msg input (i + 1) hp1, blockOff_msg input (i + 1) hp1,
            LoopCompletionControl.cont_cold input hal (i + 1), Nat.add_sub_cancel, hh, s', StaggerPersistentLoopSites.result]
            using gb.trans (gd.trans gs)
        · have he : i + 1 = count := by omega
          have hi1 : count - 1 = i := by omega
          have hlt : (msize s').toNat < (offsetWord i + UInt256.ofNat 128).toNat := hl.mpr he
          have gx := StaggerPersistentLoopSites.gasSteps_glExit s' s'.memory (hashes i) (offsetWord i) (UInt256.ofNat 48)
            rho (by omega) a.running hlt a.code a.fork a.notPrecompile
          have hI1 : I (i + 1) = exitState input s' (hashes i) h' count rho := by
            simp only [I, s', h', show ¬ (i + 1 < count) by omega, if_false, hi1]
          rw [hI1]
          simpa only [exitState, s', h', count, hi1, hoff, hcm, hc, blockCont_msg input i (UInt256.ofNat 48) hp] using gb.trans (gd.trans gx)
  have g := GasSteps.iterateBounded (I := I) count hb
  simpa only [I, if_pos hcount, if_neg (Nat.lt_irrefl count)] using g

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction

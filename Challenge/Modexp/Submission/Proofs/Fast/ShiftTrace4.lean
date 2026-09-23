import Challenge.Modexp.Submission.Proofs.Fast.ShiftProducerSplitRun
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace3
import Challenge.Modexp.Submission.Proofs.Fast.RetainedTEntry
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
import Challenge.Modexp.Submission.Proofs.Fast.M9MacShift

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

/-!
# Gas traces of the shift-reduce base conversion

Block reductions are lifted to `GasSteps` and composed: the negation loop, the
estimator prologue, the limb pass, the repair rounds, one shift step, the shift
loop, and finally the whole hit path from the dispatcher to `BDONE` together
with the miss path to the old `r0` block.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Environment facts of the carrier state, bundled. -/
structure Env (s : State) : Prop where
  code : s.executionEnv.code = Challenge.Modexp.submissionBytecode
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false
  act : 89 ≤ s.activeWords.toNat

/-- Lift a block reduction to a trace.  Every state of the routine is a record
update of the carrier `s` on `pc`, `stack` and `memory`, so the environment,
fork and halt fields are those of `s` by `rfl`. -/
def soundEnv (blk : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    {s st tt : State} (e : Env s)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock blk st = some tt)
    (henv : st.executionEnv = s.executionEnv := by rfl)
    (hforkEq : st.fork = s.fork := by rfl) (hhalt : st.halt = s.halt := by rfl) :
    Challenge.EvmProof.GasSteps st tt :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka blk
    (by rw [henv]; exact e.code) (by rw [hforkEq]; exact e.fork) h
    (by rw [hhalt]; exact e.run)
    (by rw [henv]; exact e.np)

/-- Environment certificate for an unlocated program with a proved binding. -/
def bindingEnv {s st : State} (e : Env s)
    (henv : st.executionEnv = s.executionEnv := by rfl)
    (hforkEq : st.fork = s.fork := by rfl) (hhalt : st.halt = s.halt := by rfl) :
    WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka st where
  sizeBound := by
    change Challenge.Modexp.submissionBytecode.size < 2 ^ 256
    rw [Challenge.Modexp.submissionBytecode_size]
    decide
  code := by rw [henv]; exact e.code
  forkEq := by rw [hforkEq]; exact e.fork
  running := by rw [hhalt]; exact e.run
  noPrecompile := by rw [henv]; exact e.np

theorem Env.act296 {s : State} (e : Env s) : 88 ≤ s.activeWords.toNat :=
  Nat.le_trans (by norm_num) e.act

theorem ptrWord_step (base j : Nat) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      UInt256.ofNat (Monpro.ptrAt base j) =
    UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod, Monpro.ptrAt_succ]

/-! ## The negation loop and the estimator prologue -/

/-- One negation-loop iteration with limbs to go: body, then the rotated exit test jumps back. -/
def gasSteps_negIter (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hn32 : n ≤ 8) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (negLoopState s mem n bsize esize msize j)
      (negLoopState s mem n bsize esize msize (j + 1)) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk2896a e
        (run_negBodyA s mem (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)) n bsize esize msize j
          hn32 (by omega) (negPtr_toNat n j hn32 (by omega)) e.act296 e.code e.run)).trans
      (soundEnv blk2896b e
        (run_negTail s (negStep mem n (j + 1)).memory
          (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)) (negStep mem n (j + 1)).flag
          n bsize esize msize (negPtr_ne_zero n j hn32 hj) e.code e.run)))
    rfl (by rw [negTop_succ] <;> rfl)

/-- The last limb: body, then the exit test falls through into `NEG_DONE`. -/
def gasSteps_negLast (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s) :
    Challenge.EvmProof.GasSteps (negLoopState s mem n bsize esize msize (n - 1))
      (negDoneState s mem n bsize esize msize) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk2896a e
        (run_negBodyA s mem (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) (n - 1))) n bsize esize
          msize (n - 1) hn32 (by omega) (negPtr_toNat n (n - 1) hn32 (by omega)) e.act296 e.code
          e.run)).trans
      (soundEnv blk2896b e
        (run_negExit s (negStep mem n (n - 1 + 1)).memory
          (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) (n - 1))) (negStep mem n (n - 1 + 1)).flag
          n bsize esize msize
          (by rw [negPtr_toNat n (n - 1) hn32 (by omega)]; omega) e.code e.run)))
    rfl (by rw [negTop_succ, Nat.sub_add_cancel hn] <;> rfl)

def gasSteps_negLoop (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s) :
    Challenge.EvmProof.GasSteps (negLoopState s mem n bsize esize msize 0)
      (negDoneState s mem n bsize esize msize) :=
  (Challenge.EvmProof.GasSteps.iterateBounded (I := fun j => negLoopState s mem n bsize esize msize j)
      (n - 1) (fun j hj => gasSteps_negIter s mem n bsize esize msize j hn32 (by omega) e)).trans
    (gasSteps_negLast s mem n bsize esize msize hn hn32 e)

/-- From the first `CSUB` return to the `E5` entry (slot parking done, the
esize/byte guard still pending inside `blk2764`). -/
def gasSteps_preE5 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps (afterCsub0State s mem n bsize esize msize)
      (cacheSetupState s (preMem (negStep mem n n).memory) n bsize esize msize) :=
  ((((soundEnv blk2892 e
      (run_negEntry s mem n bsize esize msize hn hn32 e.act296 hml e.code e.run)).trans
    (gasSteps_negLoop s mem n bsize esize msize hn hn32 e)).trans
    (soundEnv blk2919 e
      (run_negDone s mem n bsize esize msize e.act296 e.code e.run))).trans
    (soundEnv blk2956 e
      (run_preNewton s (negStep mem n n).memory n bsize esize msize e.code e.run))).trans
    (soundEnv blk2982 e
      (run_newtonB s (negStep mem n n).memory n bsize esize msize e.act296 e.code e.run))

/-- From the first `CSUB` return to the shift loop head with counter `n`
(word-sized exponent arm of `E5`). -/
def gasSteps_prologue (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (hfast : n = 4 ∨ n = 8)
    (hesize : UInt256.ofNat esize ≠ UInt256.ofNat 1)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps (afterCsub0State s mem n bsize esize msize)
      (shiftLoopState s
        (Exp.storeWord (Exp.storeWord (preMem (negStep mem n n).memory) 1698 (shiftEntry n)) 1760
          (UInt256.ofNat 0)) n bsize esize msize n) :=
  (gasSteps_preE5 s mem n bsize esize msize hn hn32 e hml).trans
    (soundEnv blk2764 e
      (run_e5 s (preMem (negStep mem n n).memory) n bsize esize msize hfast e.act hesize e.code
        e.run))

/-- Slow-exponent arm of `E5` (`esize = 1`, exponent byte `≠ 3`): flag 0,
counter `n`. -/
def gasSteps_prologue_slow (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (hfast : n = 4 ∨ n = 8)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyteNe : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord (preMem (negStep mem n n).memory) 2816).toNat) ≠
      UInt256.ofNat 3)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps (afterCsub0State s mem n bsize esize msize)
      (shiftLoopState s
        (Exp.storeWord (Exp.storeWord (preMem (negStep mem n n).memory) 1698 (shiftEntry n)) 1760
          (UInt256.ofNat 0)) n bsize esize msize n) :=
  (gasSteps_preE5 s mem n bsize esize msize hn hn32 e hml).trans
    (soundEnv blk2764 e
      (run_e5_slowexp s (preMem (negStep mem n n).memory) n bsize esize msize hfast e.act hsize1
        hbyteNe e.code e.run))

/-- E3 arm of `E5` (`esize = 1`, exponent byte `= 3`): flag 1, counter `n / 2`. -/
def gasSteps_prologue_e3 (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (hfast : n = 4 ∨ n = 8)
    (hsize1 : UInt256.ofNat esize = UInt256.ofNat 1)
    (hbyte3 : UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata
        (MachineState.readWord (preMem (negStep mem n n).memory) 2816).toNat) =
      UInt256.ofNat 3)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps (afterCsub0State s mem n bsize esize msize)
      (shiftLoopState s
        (Exp.storeWord (Exp.storeWord (preMem (negStep mem n n).memory) 1698 (shiftEntry n)) 1760
          (UInt256.ofNat 1)) n bsize esize msize (n / 2)) :=
  (gasSteps_preE5 s mem n bsize esize msize hn hn32 e hml).trans
    (soundEnv blk2764 e
      (run_e5_e3 s (preMem (negStep mem n n).memory) n bsize esize msize hfast e.act hsize1
        hbyte3 e.code e.run))
/-! ## The limb pass -/






/-- One add-pass iteration with limbs to go. -/
def gasSteps_addIter (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 8) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (addInnerState s mem n bsize esize msize k j)
      (addInnerState s mem n bsize esize msize k (j + 1)) :=
    (soundEnv blk3157a e
      (run_addBodyA s mem (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j)) n bsize esize msize k j
        (entrySlots mem n bsize esize ++ outer n bsize esize msize)
        hn32 (by omega) (tPtr_toNat n j hn32 (by omega))
        (by simp [entrySlots, rideSlots, shiftEntry, outer, Exp.outer])
        e.act296 e.code e.run)).trans
    (soundEnv blk3157b e
      (run_addTail_go s (addStep mem n (j + 1)).memory (addStep mem n (j + 1)).flag
        (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j))
        (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (j + 1))) n bsize esize msize k
        (entrySlots mem n bsize esize ++ outer n bsize esize msize)
        (ptrWord_step _ _)
        (by simp [entrySlots, rideSlots, shiftEntry, outer, Exp.outer])
        (tPtr_gt_8255 n (j + 1) hn32 hj) e.code e.run))

/-- The last add-pass iteration, falling into the add tail. -/
def gasSteps_addLastIter (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s) :
    Challenge.EvmProof.GasSteps (addInnerState s mem n bsize esize msize k (n - 1))
      (addTailState s mem n bsize esize msize k) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk3157a e
        (run_addBodyA s mem (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (n - 1))) n bsize esize
          msize k (n - 1) (entrySlots mem n bsize esize ++ outer n bsize esize msize)
          hn32 (by omega) (tPtr_toNat n (n - 1) hn32 (by omega))
          (by simp [entrySlots, rideSlots, shiftEntry, outer, Exp.outer]) e.act296 e.code e.run)).trans
      ((soundEnv blk3157b e
        (run_addTail_last s (addStep mem n (n - 1 + 1)).memory (addStep mem n (n - 1 + 1)).flag
          (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (n - 1)))
          (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (n - 1 + 1))) n bsize esize msize k
          (entrySlots mem n bsize esize ++ outer n bsize esize msize)
          (by simp [entrySlots, rideSlots, shiftEntry, outer, Exp.outer])
          (ptrWord_step _ _) (by rw [Nat.sub_add_cancel hn]; exact tPtr_toNat_last n hn32)
          e.code e.run)).trans
        (soundEnv blk3157c e
          (run_addPad s (addStep mem n (n - 1 + 1)).memory (addStep mem n (n - 1 + 1)).flag
            (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) (n - 1 + 1))) n bsize esize msize k
            (entrySlots mem n bsize esize ++ outer n bsize esize msize)
            e.code e.run))))
    rfl (by rw [Nat.sub_add_cancel hn]; rfl)

/-- The whole add pass from the round head to the add tail. -/
def gasSteps_addPass (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n)) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (addTailState s mem n bsize esize msize k) :=
  ((soundEnv blk3153 e
      (run_addEntry s mem n bsize esize msize k e.act296 htl e.code e.run)).trans
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun j => addInnerState s mem n bsize esize msize k j) (n - 1) (fun j hj =>
        gasSteps_addIter s mem n bsize esize msize k j hn32 (by omega) e))).trans
    (gasSteps_addLastIter s mem n bsize esize msize k hn hn32 e)

/-- One add round, from the loop head back to the loop head. -/
def gasSteps_addRound_again (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hout : addOut mem n = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (addLoopState s (addRoundMem mem n) n bsize esize msize k) :=
  (gasSteps_addPass s mem n bsize esize msize k hn hn32 e htl).trans
    (soundEnv blk3192 e
      (run_addTail_again s mem n bsize esize msize k e.act296 hout e.code e.run))

/-- The last add round, ending at `SUB_CHECK`. -/
def gasSteps_addRound_done (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hout : addOut mem n = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (subCheckState s (addRoundMem mem n) n bsize esize msize k) :=
  (gasSteps_addPass s mem n bsize esize msize k hn hn32 e htl).trans
    (soundEnv blk3192 e
      (run_addTail_done s mem n bsize esize msize k e.act296 hout e.code e.run))

/-- `c ≥ 1` add rounds, the last of which carries out. -/
def gasSteps_addRounds (s : State) (mem : ByteArray) (n bsize esize msize k c : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 8) (e : Env s) (hc : 1 ≤ c)
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hrounds : ∀ i, i < c - 1 → addOut (addRounds mem n i) n = UInt256.ofNat 0)
    (hlast : addOut (addRounds mem n (c - 1)) n = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (subCheckState s (addRounds mem n c) n bsize esize msize k) :=
  have htl' : ∀ i, MachineState.readWord (addRounds mem n i) 2784 =
      UInt256.ofNat (2080 + 32 * n) := fun i => by
    rw [addRounds_readWord_disjoint mem n 2784 (Or.inr (by omega)) i]; exact htl
  Challenge.EvmProof.GasSteps.cast
    ((Challenge.EvmProof.GasSteps.iterateBounded
        (I := fun i => addLoopState s (addRounds mem n i) n bsize esize msize k) (c - 1)
        (fun i hi =>
          gasSteps_addRound_again s (addRounds mem n i) n bsize esize msize k hn hn32 e
            (htl' i) (hrounds i hi))).trans
      (gasSteps_addRound_done s (addRounds mem n (c - 1)) n bsize esize msize k hn hn32 e
        (htl' (c - 1)) hlast))
    rfl (by
      show subCheckState s (addRounds mem n (c - 1 + 1)) n bsize esize msize k = _
      rw [show c - 1 + 1 = c from by omega])


/-! ## The `CSUB` calls -/

theorem jumpD5357 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat pcAfterCsub).toNat = true :=
  Exp.jumpD pcAfterCsub (by decide) jumpDest4839

theorem jumpD4692 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat pcCsubReturn).toNat = true :=
  Exp.jumpD pcCsubReturn (by decide) jumpDest4657

/-- `blk3253` now returns straight to the loop head: the `CSUB` it used to call is the identity
on every reachable state (`repair_lt_mm`), so the artifact does not call it.  The hypotheses the
call needed are kept so that the call sites are unchanged. -/
def gasSteps_csubStep (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hk : 1 ≤ k) (hk32 : k ≤ 32) (_hn : 2 ≤ n) (_hn32 : n ≤ 8) (e : Env s)
    (_hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (_htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (_hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (_htn : (MachineState.readWord mem 2080).toNat ≤ 1)
    (_hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (csubCallState s mem n bsize esize msize k)
      (afterCsubState s mem n bsize esize msize k) :=
    soundEnv blk3253 e (run_csubCall s mem n bsize esize msize k hk hk32 e.code e.run)
def canonicalCopyBlock : WindowTwentyOneBinding.Block Artifact.submissionArtifact .Osaka 2574
    ShiftProducerSplitRun.copyProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2091 5 2574 ShiftProducerSplitRun.copyProgram
    (by decide) (by rfl) (by rfl) (by decide)

def gasSteps_hitCsub (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (e : Env s)
    (hdata : s.executionEnv.calldata = input)
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (hitState s mem n bsize esize msize)
      (afterCsub0State s (ShiftProducerCanonical.canonicalMemory mem input n)
        n bsize esize msize) := by
  have hhigh : ∀ addr, 2688 ≤ addr →
      MachineState.readWord (hitMem mem input n) addr = MachineState.readWord mem addr := by
    intro addr haddr
    unfold hitMem ShiftProducerCanonical.hitMemory
    exact Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)
  have htn0' : MachineState.readWord (hitMem mem input n) 2080 = UInt256.ofNat 0 := by
    unfold hitMem ShiftProducerCanonical.hitMemory
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]
    exact htn0
  have hs32' : MachineState.readWord (Csub.csStep (hitMem mem input n) n n).memory 2688 =
      UInt256.ofNat (32 * n) := by
    rw [Csub.csStep_readWord_disjoint _ n 2688 (by omega) (Or.inr (by omega)) n le_rfl,
      hhigh 2688 le_rfl]
    exact hs32
  have htn' : (MachineState.readWord (Csub.csStep (hitMem mem input n) n n).memory 2080).toNat ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint _ n 2080 (by omega) (Or.inr (by omega)) n le_rfl, htn0']
    decide
  have hlen : (outer n bsize esize msize).length ≤ 1008 := by simp [outer, Exp.outer]
  have first : Challenge.EvmProof.GasSteps (hitState s mem n bsize esize msize)
      (rawCsubReturnState s (RetainedTNormalizer.resultMemory (hitMem mem input n) n) n bsize esize msize) :=
    Challenge.EvmProof.GasSteps.cast
      ((soundEnv blk2874 e
          (run_hit s mem input n bsize esize msize (by omega) hn32 e.act hdata e.code e.run)).trans
        (RetainedT.gasSteps_retained s (hitMem mem input n) n
          (UInt256.ofNat pcCsubReturn) (outer n bsize esize msize) hlen e.code e.fork e.run
          e.np e.act296 hn (by omega) jumpD4692
          (by rw [hhigh 2752 (by omega)]; exact hml)
          (by rw [hhigh 2784 (by omega)]; exact htl) hs32' htn' hfast))
      rfl rfl
  have copy := canonicalCopyBlock.steps (bindingEnv e) rfl
    (ShiftProducerSplitRun.run_copy s (RetainedTNormalizer.resultMemory (hitMem mem input n) n) n
      [UInt256.ofNat n, UInt256.ofNat bsize, UInt256.ofNat esize, UInt256.ofNat msize]
      (by simp) (by omega) hn32 e.act)
  exact first.trans (by
    simpa only [rawCsubReturnState,afterCsub0State,frameState,pcCsubReturn,pcAfterCsub0,
      ShiftProducerSplitRun.frame,outer,Exp.outer,ShiftProducerCanonical.canonicalMemory,
      ShiftProducerCanonical.reducedMemory,hitMem] using copy)

/-- The value-side facts a step needs and preserves. -/
structure StepInv (mem : ByteArray) (n bsize mm minv : Nat) : Prop where
  frame : Exp.Frame mem n bsize minv
  modulus : Model.FastRepresents mem 0 n mm
  neg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)
  cache : MachineState.readWord mem 1698 = ShiftCacheModel.entryWord n
  pre : PreOK mem

theorem negOf_cases (mem : ByteArray) (c q : UInt256) :
    negOf mem c q = UInt256.ofNat 0 ∨ negOf mem c q = UInt256.ofNat 1 := by
  unfold negOf UInt256.gt
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The step's intermediate values, as reducible abbreviations. -/
abbrev stepU (mem : ByteArray) (n : Nat) : ByteArray := uMem mem n
abbrev stepQ (mem : ByteArray) (n : Nat) : UInt256 := qhatOf (uMem mem n)
abbrev stepMac (mem : ByteArray) (n : Nat) : Monpro.MacState :=
  macOf (uMem mem n) n (qhatOf (uMem mem n))
abbrev stepMid (mem : ByteArray) (n : Nat) : ByteArray :=
  midMem (stepMac mem n).memory (stepMac mem n).carry (stepQ mem n)
abbrev stepNeg (mem : ByteArray) (n : Nat) : UInt256 :=
  negOf (stepMac mem n).memory (stepMac mem n).carry (stepQ mem n)

/-- One shift step: from the loop head with `k ≥ 1` steps to go back to the loop
head with `k - 1`, the memory advanced by `stepMem`. -/
def gasSteps_step (s : State) (mem : ByteArray) (n bsize esize msize k mm minv : Nat)
    {r : Nat}
    (hk : 1 ≤ k) (hk32 : k ≤ 32) (hn : 2 ≤ n) (hn32 : n ≤ 8) (hbs : bsize = 32 * n)
    (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (e : Env s)
    (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm)
    (rf : RepairFacts
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))))
    (hfast : n = 4 ∨ n = 8) :
    Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize k)
      (shiftLoopState s (stepMem mem n mm) n bsize esize msize (k - 1)) := by
  have rf' : RepairFacts (stepMid mem n) n mm (stepNeg mem n) := rf
  -- frame words along the way
  have htl0 : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n) := inv.frame.tl
  have hml0 : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32) := inv.frame.ml
  have hs320 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n) := inv.frame.s32
  have hhighU : ∀ addr, 2688 ≤ addr →
      MachineState.readWord (stepU mem n) addr = MachineState.readWord mem addr :=
    fun addr haddr => uMem_readWord_disjoint mem n addr (Or.inr (by omega))
  have hhighMid : ∀ addr, 2688 ≤ addr →
      MachineState.readWord (stepMid mem n) addr = MachineState.readWord mem addr := by
    intro addr haddr
    show MachineState.readWord (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) addr = _
    unfold midMem Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    unfold macOf
    rw [l1Step_readWord_disjoint (uMem mem n) (qhatOf (uMem mem n)) NEG n addr (by omega)
      (Or.inr (by omega)) n]
    exact hhighU addr haddr
  have hhighFix : ∀ addr, 2688 ≤ addr →
      MachineState.readWord (fixMem (stepMid mem n) n mm (stepNeg mem n)) addr =
        MachineState.readWord mem addr := by
    intro addr haddr
    rw [fixMem_readWord_disjoint (stepMid mem n) n mm (stepNeg mem n) addr (Or.inr (by omega))]
    exact hhighMid addr haddr
  -- the chain
  -- The old chain ran three blocks, then a mac setup block, then a four-cell dispatch, then the
  -- pointer loop. The rewritten artifact ends the prefix at the estimate block and reaches the
  -- conversion entry directly, so `g1` stops at `macSetupState` (pc 2673) and `g2` is the single
  -- section lemma over the eight straight blocks.
  have g1 : Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize k)
      (macSetupState s mem n bsize esize msize k) :=
    ((soundEnv blk3013 e
        (run_shiftHead_go s mem n bsize esize msize k (by omega) hk32 e.code e.run)).trans
      (soundEnv blk3018 e
        (run_shiftBody s mem n bsize esize msize k hn hn32 e.act hbs htl0 e.code e.run))).trans
      (soundEnv blk3026 e
        (run_estimate s mem n bsize esize msize k e.act296 e.code e.run))
  have g2 : Challenge.EvmProof.GasSteps
      (macSetupState s mem n bsize esize msize k)
      (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k) :=
    M9Mac.gasSteps_macSection n hfast s (stepU mem n) (stepQ mem n) bsize esize msize k
      e.run e.code e.fork e.np e.act296
  have htlMid : MachineState.readWord (stepMid mem n) 2784 = UInt256.ofNat (2080 + 32 * n) := by
    rw [hhighMid 2784 (by omega)]; exact htl0
  have htlA : MachineState.readWord
      (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n))) 2784 =
      UInt256.ofNat (2080 + 32 * n) := by
    rw [addRounds_readWord_disjoint (stepMid mem n) n 2784 (Or.inr (by omega))]; exact htlMid
  -- The subtract repair rounds are unreachable: with the estimate never under-shooting,
  -- `ShiftModel.fixMem_subCount_zero` shows the value after the (possibly empty) add
  -- rounds is already below `radix ^ n` (so `subCount` is zero and `fixMem` is exactly
  -- the add rounds), and `ShiftModel.mid_neg_tn_zero` shows the top-limb word is zero
  -- outright when the sign flag is clear.  The artifact's subtract-round blocks sit on
  -- dead branches and their jump targets were never maintained.
  have hmodU : Model.FastRepresents (stepU mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 inv.modulus
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by omega))
  have hnegU : Model.FastRepresents (stepU mem n) NEG n (Limbs.radix ^ n - mm) := by
    refine (Model.fastRepresents_congr ?_ _).2 inv.neg
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega))
  have hu : tv (stepU mem n) n = r * Limbs.radix := uMem_tv mem n r hn hn32 hbase
  have hulo : r * Limbs.radix < Limbs.radix ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (lt_trans hr hmm) Limbs.radix_pos
  obtain ⟨hrel, hltmid, hneg1⟩ :=
    mid_relation (stepU mem n) n mm (stepQ mem n) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  have hmodMid : Model.FastRepresents (stepMid mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmodU
    intro i hi
    show MachineState.readWord (Exp.storeWord _ 2080 _) _ = _
    unfold Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    exact mac_readWord_disjoint (stepU mem n) n _ _ (by omega) (Or.inl (by omega))
  have hqge : (r * Limbs.radix) / mm ≤ (stepQ mem n).toNat :=
    qhatOf_ge (stepU mem n) n mm (r * Limbs.radix) hn hn32 htop hmodU
      (PreOK_uMem mem n hn32 inv.pre) hu
      (Nat.mul_lt_mul_of_pos_right hr Limbs.radix_pos)
  obtain ⟨hsc0, _hltA, hfixEq⟩ :=
    fixMem_subCount_zero (stepMid mem n) n mm (stepNeg mem n) (r * Limbs.radix)
      (stepQ mem n).toNat (by omega : 1 ≤ n) hn32 hmpos hmm hmodMid hrel hltmid hneg1 hqge
  have htnA : (MachineState.readWord
      (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n))) 2080).toNat = 0 := by
    have h := rf'.subDoneTn
    rw [hfixEq] at h
    exact h
  have tail : Challenge.EvmProof.GasSteps
      (subCheckState s
        (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
        n bsize esize msize k)
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k) :=
    Challenge.EvmProof.GasSteps.cast
      (soundEnv blk3204 e
        (run_subCheck_done s
          (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
          n bsize esize msize k e.act296 htnA e.code e.run))
      rfl (by rw [hfixEq])
  have g3 : Challenge.EvmProof.GasSteps
      (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k) := by
    by_cases h0 : stepNeg mem n = UInt256.ofNat 0
    · -- `neg = 0`: the top-limb word is zero (`ShiftModel.mid_neg_tn_zero`), so the
      -- middle block falls straight into the `CSUB` call; `fixMem` is the identity.
      have htz : tnOf (stepMac mem n).memory (stepMac mem n).carry (stepQ mem n) =
          UInt256.ofNat 0 :=
        mid_neg_tn_zero mem n mm r hn hn32 hmpos hmm htop inv.modulus inv.neg hbase hr
          inv.pre h0
      have hfix : fixMem (stepMid mem n) n mm (stepNeg mem n) = stepMid mem n := by
        rw [hfixEq, rf'.posCount h0, addRounds_zero]
      have start : Challenge.EvmProof.GasSteps
          (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
          (csubCallState s (stepMid mem n) n bsize esize msize k) :=
        soundEnv blk3125 e
          (run_mid_zero s (stepU mem n) (stepQ mem n) n bsize esize msize k hn32 e.act296 h0 htz
            e.code e.run)
      exact Challenge.EvmProof.GasSteps.cast start rfl (by rw [hfix])
    · have h1 : stepNeg mem n = UInt256.ofNat 1 :=
        (negOf_cases (stepMac mem n).memory (stepMac mem n).carry (stepQ mem n)).resolve_left h0
      have hc1 : 1 ≤ addCount (stepMid mem n) n mm (stepNeg mem n) := rf'.negCount h1
      have hnz : (stepNeg mem n).toNat ≠ 0 := by rw [h1] <;> decide
      have start : Challenge.EvmProof.GasSteps
          (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
          (addLoopState s (stepMid mem n) n bsize esize msize k) :=
        (soundEnv blk3125 e
          (run_mid_unc s (stepU mem n) (stepQ mem n) n bsize esize msize k hn32 e.act296
            (Or.inl hnz) e.code e.run)).trans
        (soundEnv blkUnc e
          (run_unc_add s (stepMid mem n) n bsize esize msize k (stepNeg mem n) hnz e.code e.run))
      have adds := gasSteps_addRounds s (stepMid mem n) n bsize esize msize k
        (addCount (stepMid mem n) n mm (stepNeg mem n)) (by omega) hn32 e hc1 htlMid
        rf'.addRoundsOut (rf'.addLastOut hc1)
      exact (start.trans adds).trans tail
  have g4 : Challenge.EvmProof.GasSteps
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k)
      (afterCsubState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k) :=
    gasSteps_csubStep s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k
      hk hk32 hn hn32 e
      (by rw [hhighFix 2752 (by omega)]; exact hml0)
      (by rw [hhighFix 2784 (by omega)]; exact htl0)
      (by rw [hhighFix 2688 le_rfl]; exact hs320)
      (by rw [rf'.subDoneTn]; decide)
      hfast
  -- `CSUB` returns to the loop head with `k - 1`: `afterCsubState k` is `shiftLoopState (k - 1)`.
  exact Challenge.EvmProof.GasSteps.cast (((g1.trans g2).trans g3).trans g4) rfl rfl

end Challenge.Modexp.Submission.Proofs.Fast.Shift

import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace3

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
  act : 298 ≤ s.activeWords.toNat

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

theorem Env.act296 {s : State} (e : Env s) : 296 ≤ s.activeWords.toNat :=
  Nat.le_trans (by norm_num) e.act

/-! ## The negation loop and the estimator prologue -/

/-- One negation-loop iteration with limbs to go: body, exit test, decrement. -/
def gasSteps_negIter (s : State) (mem : ByteArray) (n bsize esize msize j : Nat)
    (hn32 : n ≤ 32) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (negLoopState s mem n bsize esize msize j)
      (negLoopState s mem n bsize esize msize (j + 1)) :=
  ((soundEnv blk2896a e
      (run_negBodyA s mem (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)) n bsize esize msize j
        hn32 (by omega) (negPtr_toNat n j hn32 (by omega)) e.act296 e.code e.run)).trans
    (soundEnv blk2896b e
      (run_negTail s (negStep mem n (j + 1)).memory
        (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)) (negStep mem n (j + 1)).flag
        n bsize esize msize (negPtr_ne_zero n j hn32 hj) e.code e.run))).trans
    (soundEnv blk2915 e
      (run_negNext s mem n bsize esize msize j e.code e.run))

def gasSteps_negLoop (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) :
    Challenge.EvmProof.GasSteps (negLoopState s mem n bsize esize msize 0)
      (negDoneState s mem n bsize esize msize) :=
  (Challenge.EvmProof.GasSteps.iterateBounded (I := fun j => negLoopState s mem n bsize esize msize j)
      (n - 1) (fun j hj => gasSteps_negIter s mem n bsize esize msize j hn32 (by omega) e)).trans
    (soundEnv blk2896 e
      (run_negLast s mem n bsize esize msize hn hn32 e.act296 e.code e.run))

/-- From the first `CSUB` return to the shift loop head with `k = n`. -/
def gasSteps_prologue (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32)) :
    Challenge.EvmProof.GasSteps (afterCsub0State s mem n bsize esize msize)
      (shiftLoopState s (preMem (negStep mem n n).memory) n bsize esize msize n) :=
  ((((soundEnv blk2892 e
      (run_negEntry s mem n bsize esize msize hn hn32 e.act296 hml e.code e.run)).trans
    (gasSteps_negLoop s mem n bsize esize msize hn hn32 e)).trans
    (soundEnv blk2919 e
      (run_negDone s mem n bsize esize msize e.act296 e.code e.run))).trans
    (soundEnv blk2956 e
      (run_preNewton s (negStep mem n n).memory n bsize esize msize e.code e.run))).trans
    (soundEnv blk2982 e
      (run_newtonB s (negStep mem n n).memory n bsize esize msize e.act296 e.code e.run))

/-! ## The limb pass -/

/-- One limb-pass iteration with limbs to go. -/
def gasSteps_macIter (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 32) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (macLoopState s um q n bsize esize msize k j)
      (macLoopState s um q n bsize esize msize k (j + 1)) :=
  (soundEnv blk3077a e
      (run_macBodyA s um q (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) j))
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j))
        (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) (j + 1)))
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (j + 1)))
        n bsize esize msize k j e.run e.code e.act296 hn32 (by omega)
        (aPtr_toNat n j hn32 (by omega)) (tPtr_toNat n j hn32 (by omega))
        (ptrAt_step _ _) (ptrAt_step _ _))).trans
    (soundEnv blk3077b e
      (run_macTail_go s (Monpro.l1Step um q NEG n (j + 1)).memory
        (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) (j + 1)))
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (j + 1)))
        (Monpro.l1Step um q NEG n (j + 1)).carry q n bsize esize msize k
        (tPtr_gt_8224 n (j + 1) hn32 hj) e.code e.run))

/-- The last limb-pass iteration, falling into the middle block. -/
def gasSteps_macLast (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) :
    Challenge.EvmProof.GasSteps (macLoopState s um q n bsize esize msize k (n - 1))
      (midState s um q n bsize esize msize k) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk3077a e
        (run_macBodyA s um q (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) (n - 1)))
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1)))
          (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) (n - 1 + 1)))
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1 + 1)))
          n bsize esize msize k (n - 1) e.run e.code e.act296 hn32 (by omega)
          (aPtr_toNat n (n - 1) hn32 (by omega)) (tPtr_toNat n (n - 1) hn32 (by omega))
          (ptrAt_step _ _) (ptrAt_step _ _))).trans
      (soundEnv blk3077b e
        (run_macTail_exit s (Monpro.l1Step um q NEG n (n - 1 + 1)).memory
          (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) (n - 1 + 1)))
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1 + 1)))
          (Monpro.l1Step um q NEG n (n - 1 + 1)).carry q n bsize esize msize k
          (by rw [Nat.sub_add_cancel hn]; exact tPtr_toNat_last n hn32) e.code e.run)))
    rfl (by rw [Nat.sub_add_cancel hn]; rfl)

def gasSteps_macLoop (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) :
    Challenge.EvmProof.GasSteps (macLoopState s um q n bsize esize msize k 0)
      (midState s um q n bsize esize msize k) :=
  (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun j => macLoopState s um q n bsize esize msize k j) (n - 1) (fun j hj =>
        gasSteps_macIter s um q n bsize esize msize k j hn32 (by omega) e)).trans
    (gasSteps_macLast s um q n bsize esize msize k hn hn32 e)

/-! ## The repair rounds -/

/-- One add-pass iteration with limbs to go. -/
def gasSteps_addIter (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 32) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (addInnerState s mem n bsize esize msize k j)
      (addInnerState s mem n bsize esize msize k (j + 1)) :=
  (soundEnv blk3157a e
      (run_addBodyA s mem (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j)) n bsize esize msize k j
        hn32 (by omega) (tPtr_toNat n j hn32 (by omega)) e.act296 e.code e.run)).trans
    (soundEnv blk3157b e
      (run_addTail_go s (addStep mem n (j + 1)).memory (addStep mem n (j + 1)).flag
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j))
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (j + 1))) n bsize esize msize k
        (ptrAt_step _ _) (tPtr_gt_8255 n (j + 1) hn32 hj) e.code e.run))

/-- The last add-pass iteration, falling into the add tail. -/
def gasSteps_addLastIter (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) :
    Challenge.EvmProof.GasSteps (addInnerState s mem n bsize esize msize k (n - 1))
      (addTailState s mem n bsize esize msize k) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk3157a e
        (run_addBodyA s mem (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1))) n bsize esize
          msize k (n - 1) hn32 (by omega) (tPtr_toNat n (n - 1) hn32 (by omega)) e.act296 e.code
          e.run)).trans
      (soundEnv blk3157b e
        (run_addTail_last s (addStep mem n (n - 1 + 1)).memory (addStep mem n (n - 1 + 1)).flag
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1)))
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1 + 1))) n bsize esize msize k
          (ptrAt_step _ _) (by rw [Nat.sub_add_cancel hn]; exact tPtr_toNat_last n hn32)
          e.code e.run)))
    rfl (by rw [Nat.sub_add_cancel hn]; rfl)

/-- The whole add pass from the round head to the add tail. -/
def gasSteps_addPass (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
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
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hout : addOut mem n = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (addLoopState s (addRoundMem mem n) n bsize esize msize k) :=
  (gasSteps_addPass s mem n bsize esize msize k hn hn32 e htl).trans
    (soundEnv blk3192 e
      (run_addTail_again s mem n bsize esize msize k e.act296 hout e.code e.run))

/-- The last add round, ending at `SUB_CHECK`. -/
def gasSteps_addRound_done (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hout : addOut mem n = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (subCheckState s (addRoundMem mem n) n bsize esize msize k) :=
  (gasSteps_addPass s mem n bsize esize msize k hn hn32 e htl).trans
    (soundEnv blk3192 e
      (run_addTail_done s mem n bsize esize msize k e.act296 hout e.code e.run))

/-- `c ≥ 1` add rounds, the last of which carries out. -/
def gasSteps_addRounds (s : State) (mem : ByteArray) (n bsize esize msize k c : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) (hc : 1 ≤ c)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hrounds : ∀ i, i < c - 1 → addOut (addRounds mem n i) n = UInt256.ofNat 0)
    (hlast : addOut (addRounds mem n (c - 1)) n = UInt256.ofNat 1) :
    Challenge.EvmProof.GasSteps (addLoopState s mem n bsize esize msize k)
      (subCheckState s (addRounds mem n c) n bsize esize msize k) :=
  have htl' : ∀ i, MachineState.readWord (addRounds mem n i) 9440 =
      UInt256.ofNat (8224 + 32 * n) := fun i => by
    rw [addRounds_readWord_disjoint mem n 9440 (Or.inr (by omega)) i]; exact htl
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

/-- One subtract-pass iteration with limbs to go. -/
def gasSteps_subIter (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat)
    (hn32 : n ≤ 32) (hj : j + 1 < n) (e : Env s) :
    Challenge.EvmProof.GasSteps (subInnerState s mem n bsize esize msize k j)
      (subInnerState s mem n bsize esize msize k (j + 1)) :=
  (soundEnv blk3213a e
      (run_subBodyA s mem (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j)) n bsize esize msize k j
        hn32 (by omega) (tPtr_toNat n j hn32 (by omega)) e.act296 e.code e.run)).trans
    (soundEnv blk3213b e
      (run_subTail_go s (subStep mem n (j + 1)).memory (subStep mem n (j + 1)).flag
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j))
        (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (j + 1))) (subStep mem n j).flag
        n bsize esize msize k
        (ptrAt_step _ _) (tPtr_gt_8255 n (j + 1) hn32 hj) e.code e.run))

/-- The last subtract-pass iteration, falling into the subtract tail. -/
def gasSteps_subLastIter (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s) :
    Challenge.EvmProof.GasSteps (subInnerState s mem n bsize esize msize k (n - 1))
      (subTailState s mem n bsize esize msize k) :=
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk3213a e
        (run_subBodyA s mem (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1))) n bsize esize
          msize k (n - 1) hn32 (by omega) (tPtr_toNat n (n - 1) hn32 (by omega)) e.act296 e.code
          e.run)).trans
      (soundEnv blk3213b e
        (run_subTail_last s (subStep mem n (n - 1 + 1)).memory (subStep mem n (n - 1 + 1)).flag
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1)))
          (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) (n - 1 + 1))) (subStep mem n (n - 1)).flag
          n bsize esize msize k
          (ptrAt_step _ _) (by rw [Nat.sub_add_cancel hn]; exact tPtr_toNat_last n hn32)
          e.code e.run)))
    rfl (by rw [Nat.sub_add_cancel hn]; rfl)

/-- One subtract round, from `SUB_CHECK` with `TN ≠ 0` back to `SUB_CHECK`. -/
def gasSteps_subRound (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (htn : (MachineState.readWord mem 8224).toNat ≠ 0) :
    Challenge.EvmProof.GasSteps (subCheckState s mem n bsize esize msize k)
      (subCheckState s (subRoundMem mem n) n bsize esize msize k) :=
  ((((soundEnv blk3204 e
      (run_subCheck_go s mem n bsize esize msize k e.act296 htn e.code e.run)).trans
    (soundEnv blk3210 e
      (run_subEntry s mem n bsize esize msize k e.act296 htl e.code e.run))).trans
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun j => subInnerState s mem n bsize esize msize k j) (n - 1) (fun j hj =>
        gasSteps_subIter s mem n bsize esize msize k j hn32 (by omega) e))).trans
    (gasSteps_subLastIter s mem n bsize esize msize k hn hn32 e)).trans
    (soundEnv blk3245 e
      (run_subTail s mem n bsize esize msize k e.act296 e.code e.run))

/-- `c` subtract rounds followed by the exit to the `CSUB` call. -/
def gasSteps_subRounds (s : State) (mem : ByteArray) (n bsize esize msize k c : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hrounds : ∀ i, i < c → (MachineState.readWord (subRounds mem n i) 8224).toNat ≠ 0)
    (hdone : (MachineState.readWord (subRounds mem n c) 8224).toNat = 0) :
    Challenge.EvmProof.GasSteps (subCheckState s mem n bsize esize msize k)
      (csubCallState s (subRounds mem n c) n bsize esize msize k) :=
  have htl' : ∀ i, MachineState.readWord (subRounds mem n i) 9440 =
      UInt256.ofNat (8224 + 32 * n) := fun i => by
    rw [subRounds_readWord_disjoint mem n 9440 (Or.inr (by omega)) i]; exact htl
  (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => subCheckState s (subRounds mem n i) n bsize esize msize k) c
      (fun i hi =>
        gasSteps_subRound s (subRounds mem n i) n bsize esize msize k hn hn32 e (htl' i)
          (hrounds i hi))).trans
    (soundEnv blk3204 e
      (run_subCheck_done s (subRounds mem n c) n bsize esize msize k e.act296 hdone e.code e.run))

/-! ## The `CSUB` calls -/

theorem jumpD5357 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat pcAfterCsub).toNat = true :=
  Exp.jumpD pcAfterCsub (by decide) jumpDest5322

theorem jumpD4692 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat pcAfterCsub0).toNat = true :=
  Exp.jumpD pcAfterCsub0 (by decide) jumpDest4657

/-- `CSUB(BASE)` from the routine's call block back to `AFTER_CSUB`. -/
def gasSteps_csubStep (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htn : (MachineState.readWord mem 8224).toNat ≤ 1) :
    Challenge.EvmProof.GasSteps (csubCallState s mem n bsize esize msize k)
      (afterCsubState s (Csub.csResultMemory mem n 2048) n bsize esize msize k) :=
  have hs32' : MachineState.readWord (Csub.csStep mem n n).memory 9344 =
      UInt256.ofNat (32 * n) := by
    rw [Csub.csStep_readWord_disjoint mem n 9344 (by omega) (Or.inr (by omega)) n le_rfl]
    exact hs32
  have htn' : (MachineState.readWord (Csub.csStep mem n n).memory 8224).toNat ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint mem n 8224 (by omega) (Or.inr (by omega)) n le_rfl]
    exact htn
  have hlen : (UInt256.ofNat k :: outer n bsize esize msize).length ≤ 1008 := by
    simp [outer, Exp.outer]
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk3253 e
        (run_csubCall s mem n bsize esize msize k e.code e.run)).trans
      (Csub.gasSteps_csub s mem n (UInt256.ofNat 2048) (UInt256.ofNat pcAfterCsub)
        (UInt256.ofNat k :: outer n bsize esize msize) hlen e.code e.fork e.run e.np
        e.act296 hn hn32 jumpD5357 hml htl hs32'
        (by rw [show (UInt256.ofNat 2048).toNat = 2048 by decide]; omega) htn'))
    rfl (by
      rw [Csub.csReturnedState_eq_result,
        show (UInt256.ofNat 2048).toNat = 2048 by decide]
      rfl)

/-- The first `CSUB(BASE)`, reducing the raw base, from `HIT` to `AFTER_CSUB0`. -/
def gasSteps_hitCsub (s : State) (mem input : ByteArray) (n bsize esize msize : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (hdata : s.executionEnv.calldata = input)
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n))
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n)) :
    Challenge.EvmProof.GasSteps (hitState s mem n bsize esize msize)
      (afterCsub0State s (Csub.csResultMemory (hitMem mem input n) n 2048)
        n bsize esize msize) :=
  have hhigh : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (hitMem mem input n) addr = MachineState.readWord mem addr := by
    intro addr haddr
    unfold hitMem Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]
    exact FullBase.copyBaseMem_readWord_high mem input n addr hn32 (by omega)
  have htn0 : MachineState.readWord (hitMem mem input n) 8224 = UInt256.ofNat 0 := by
    unfold hitMem Exp.storeWord
    exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _
  have hs32' : MachineState.readWord (Csub.csStep (hitMem mem input n) n n).memory 9344 =
      UInt256.ofNat (32 * n) := by
    rw [Csub.csStep_readWord_disjoint _ n 9344 (by omega) (Or.inr (by omega)) n le_rfl,
      hhigh 9344 le_rfl]
    exact hs32
  have htn' : (MachineState.readWord (Csub.csStep (hitMem mem input n) n n).memory 8224).toNat
      ≤ 1 := by
    rw [Csub.csStep_readWord_disjoint _ n 8224 (by omega) (Or.inr (by omega)) n le_rfl, htn0]
    decide
  have hlen : (outer n bsize esize msize).length ≤ 1008 := by simp [outer, Exp.outer]
  Challenge.EvmProof.GasSteps.cast
    ((soundEnv blk2874 e
        (run_hit s mem input n bsize esize msize (by omega) hn32 e.act hdata e.code e.run)).trans
      (Csub.gasSteps_csub s (hitMem mem input n) n (UInt256.ofNat 2048)
        (UInt256.ofNat pcAfterCsub0) (outer n bsize esize msize) hlen e.code e.fork e.run
        e.np e.act296 hn hn32 jumpD4692
        (by rw [hhigh 9408 (by omega)]; exact hml)
        (by rw [hhigh 9440 (by omega)]; exact htl) hs32'
        (by rw [show (UInt256.ofNat 2048).toNat = 2048 by decide]; omega) htn'))
    rfl (by
      rw [Csub.csReturnedState_eq_result,
        show (UInt256.ofNat 2048).toNat = 2048 by decide]
      rfl)

/-! ## One shift step -/

/-- The value-side facts a step needs and preserves. -/
structure StepInv (mem : ByteArray) (n bsize mm minv : Nat) : Prop where
  frame : Exp.Frame mem n bsize minv
  modulus : Model.FastRepresents mem 0 n mm
  neg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)

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
    (hk : 1 ≤ k) (hk32 : k ≤ 32) (hn : 2 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (inv : StepInv mem n bsize mm minv)
    (rf : RepairFacts
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))) :
    Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize k)
      (shiftLoopState s (stepMem mem n mm) n bsize esize msize (k - 1)) := by
  have rf' : RepairFacts (stepMid mem n) n mm (stepNeg mem n) := rf
  -- frame words along the way
  have htl0 : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n) := inv.frame.tl
  have hml0 : MachineState.readWord mem 9408 = UInt256.ofNat (32 * n - 32) := inv.frame.ml
  have hs320 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n) := inv.frame.s32
  have hhighU : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (stepU mem n) addr = MachineState.readWord mem addr :=
    fun addr haddr => uMem_readWord_disjoint mem n addr (Or.inr (by omega))
  have hhighMid : ∀ addr, 9344 ≤ addr →
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
  have hhighFix : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (fixMem (stepMid mem n) n mm (stepNeg mem n)) addr =
        MachineState.readWord mem addr := by
    intro addr haddr
    rw [fixMem_readWord_disjoint (stepMid mem n) n mm (stepNeg mem n) addr (Or.inr (by omega))]
    exact hhighMid addr haddr
  -- the chain
  have g1 : Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize k)
      (macLoopState s (stepU mem n) (stepQ mem n) n bsize esize msize k 0) :=
    (((soundEnv blk3013 e
        (run_shiftHead_go s mem n bsize esize msize k (by omega) hk32 e.code e.run)).trans
      (soundEnv blk3018 e
        (run_shiftBody s mem n bsize esize msize k hn hn32 e.act htl0 e.code e.run))).trans
      (soundEnv blk3026 e
        (run_estimate s mem n bsize esize msize k e.act296 e.code e.run))).trans
      (soundEnv blk3069 e
        (run_macSetup s mem n bsize esize msize k (by omega) hn32 e.act296
          (by rw [hhighU 9440 (by omega)]; exact htl0)
          (by rw [hhighU 9408 (by omega)]; exact hml0) e.code e.run))
  have g2 : Challenge.EvmProof.GasSteps
      (macLoopState s (stepU mem n) (stepQ mem n) n bsize esize msize k 0)
      (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k) :=
    gasSteps_macLoop s (stepU mem n) (stepQ mem n) n bsize esize msize k (by omega) hn32 e
  have htlMid : MachineState.readWord (stepMid mem n) 9440 = UInt256.ofNat (8224 + 32 * n) := by
    rw [hhighMid 9440 (by omega)]; exact htl0
  have htlA : MachineState.readWord
      (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n))) 9440 =
      UInt256.ofNat (8224 + 32 * n) := by
    rw [addRounds_readWord_disjoint (stepMid mem n) n 9440 (Or.inr (by omega))]; exact htlMid
  have tail : Challenge.EvmProof.GasSteps
      (subCheckState s
        (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
        n bsize esize msize k)
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k) :=
    gasSteps_subRounds s
      (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
      n bsize esize msize k
      (subCount (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
        n mm)
      (by omega) hn32 e htlA rf'.subRoundsTn rf'.subDoneTn
  have g3 : Challenge.EvmProof.GasSteps
      (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k) := by
    by_cases h0 : stepNeg mem n = UInt256.ofNat 0
    · have hc0 : addCount (stepMid mem n) n mm (stepNeg mem n) = 0 := rf'.posCount h0
      have start : Challenge.EvmProof.GasSteps
          (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
          (subCheckState s (stepMid mem n) n bsize esize msize k) :=
        soundEnv blk3125 e
          (run_mid_pos s (stepU mem n) (stepQ mem n) n bsize esize msize k e.act296 h0
            e.code e.run)
      have start' : Challenge.EvmProof.GasSteps
          (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
          (subCheckState s
            (addRounds (stepMid mem n) n (addCount (stepMid mem n) n mm (stepNeg mem n)))
            n bsize esize msize k) :=
        Challenge.EvmProof.GasSteps.cast start rfl (by rw [hc0, addRounds_zero])
      exact start'.trans tail
    · have h1 : stepNeg mem n = UInt256.ofNat 1 :=
        (negOf_cases (stepMac mem n).memory (stepMac mem n).carry (stepQ mem n)).resolve_left h0
      have hc1 : 1 ≤ addCount (stepMid mem n) n mm (stepNeg mem n) := rf'.negCount h1
      have start : Challenge.EvmProof.GasSteps
          (midState s (stepU mem n) (stepQ mem n) n bsize esize msize k)
          (addLoopState s (stepMid mem n) n bsize esize msize k) :=
        soundEnv blk3125 e
          (run_mid_neg s (stepU mem n) (stepQ mem n) n bsize esize msize k e.act296 h1
            e.code e.run)
      have adds := gasSteps_addRounds s (stepMid mem n) n bsize esize msize k
        (addCount (stepMid mem n) n mm (stepNeg mem n)) (by omega) hn32 e hc1 htlMid
        rf'.addRoundsOut (rf'.addLastOut hc1)
      exact (start.trans adds).trans tail
  have g4 : Challenge.EvmProof.GasSteps
      (csubCallState s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k)
      (afterCsubState s (Csub.csResultMemory (fixMem (stepMid mem n) n mm (stepNeg mem n)) n 2048)
        n bsize esize msize k) :=
    gasSteps_csubStep s (fixMem (stepMid mem n) n mm (stepNeg mem n)) n bsize esize msize k
      hn hn32 e
      (by rw [hhighFix 9408 (by omega)]; exact hml0)
      (by rw [hhighFix 9440 (by omega)]; exact htl0)
      (by rw [hhighFix 9344 le_rfl]; exact hs320)
      (by rw [rf'.subDoneTn]; decide)
  have g5 : Challenge.EvmProof.GasSteps
      (afterCsubState s (Csub.csResultMemory (fixMem (stepMid mem n) n mm (stepNeg mem n)) n 2048)
        n bsize esize msize k)
      (shiftLoopState s (Csub.csResultMemory (fixMem (stepMid mem n) n mm (stepNeg mem n)) n 2048)
        n bsize esize msize (k - 1)) :=
    soundEnv blk3258 e
      (run_afterCsub s _ n bsize esize msize k hk hk32 e.code e.run)
  exact (((g1.trans g2).trans g3).trans g4).trans g5

end Challenge.Modexp.Submission.Proofs.Fast.Shift

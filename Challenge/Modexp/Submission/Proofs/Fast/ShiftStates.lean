import Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollEntry
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Block-boundary states of the shift-reduce base conversion

Every state is stated over an arbitrary carrier `s` and overrides only `pc`,
`stack` and `memory`.  The outer frame `outer n bsize esize msize` sits at the
bottom throughout.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

abbrev outer := Exp.outer

/-- Program counters of the appended routine. -/
def pcDispatch : Nat := 3337
def pcHit : Nat := 3352
-- 3381, not ticket 4's 3358: the recogniser-miss JUMPDEST is instruction 2597 here (it was 2602),
-- and this is the one pc in the table the regenerator could not rewrite, because 3358 has no image
-- in the pc map -- R-ONE2 deleted the instruction it used to sit on, so the map row is empty and
-- the literal was left standing.  `ShiftPCs.pc2889` states instruction 2597's pc as 3381 by `rfl`,
-- and `blk2889` is located there, so a stale 3358 makes `runLocatedBlock blk2889 (missState …)`
-- return `none`.  Nothing but the build checked this def: it is a bare `Nat` with no tie to the
-- artifact, unlike every `instructionPC`/`opAt`/`pushAt` fact around it.
def pcMiss : Nat := 3381
def pcAfterCsub0 : Nat := 3398
def pcNegLoop : Nat := 3405
def pcNegNext : Nat := 3428
/-- The negation body after its store, before the exit test. -/
def pcNegMid : Nat := 3422
def pcNegDone : Nat := 3436
def pcPreNewton : Nat := 3482
def pcNewtonB : Nat := 3507
def pcShiftLoop : Nat := 3560
def pcShiftBody : Nat := 3567
def pcEstimate : Nat := 3581
def pcMacSetup : Nat := 3663
def pcMacLoop : Nat := 3684
def pcMid : Nat := 3849
/-- The limb-pass body after the pointer steps, before the exit test. -/
def pcMacTail : Nat := 3840
def pcAddLoop : Nat := 3884
def pcAddInner : Nat := 3890
def pcAddTail : Nat := 3933
/-- The add body after `OR`, before the pointer step and exit test. -/
def pcAddMid : Nat := 3919
def pcSubCheck : Nat := 3951
def pcSubEntry : Nat := 3961
def pcSubInner : Nat := 3966
def pcSubTail : Nat := 4005
/-- The subtract body after `OR`, before the pointer step and exit test. -/
def pcSubMid : Nat := 3990
def pcCsubCall : Nat := 4019
def pcAfterCsub : Nat := 4030
def pcShiftDone : Nat := 4038

/-- A state with the outer frame only. -/
def frameState (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := mem }

/-- A state with one counter word above the outer frame. -/
def kState (s : State) (mem : ByteArray) (pc k : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- The dispatcher entry (pc 3985), reached from `R1B` with the outer frame. -/
def dispState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcDispatch n bsize esize msize

def hitState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcHit n bsize esize msize

def missState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcMiss n bsize esize msize

/-- Back from the first `CSUB`, with `BASE = b mod m`. -/
def afterCsub0State (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcAfterCsub0 n bsize esize msize

/-- The negation loop head after `j` limbs: `[p, carry]` above the frame. -/
def negLoopState (s : State) (mem : ByteArray) (n bsize esize msize j : Nat) : State :=
  { s with pc := UInt256.ofNat pcNegLoop
           stack := UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j) ::
             (negStep mem n j).flag :: outer n bsize esize msize
           memory := (negStep mem n j).memory }

/-- The pointer decrement block after limb `j` was stored. -/
def negNextState (s : State) (mem : ByteArray) (n bsize esize msize j : Nat) : State :=
  { s with pc := UInt256.ofNat pcNegNext
           stack := UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j) ::
             (negStep mem n (j + 1)).flag :: outer n bsize esize msize
           memory := (negStep mem n (j + 1)).memory }

/-- `NEG_DONE`: all `n` limbs stored, the zero pointer and the carry still live. -/
def negDoneState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcNegDone
           stack := UInt256.ofNat 0 :: (negStep mem n n).flag :: outer n bsize esize msize
           memory := (negStep mem n n).memory }

/-- `PRE_NEWTON`: `[dodd, L, d]` above the frame, four words stored. -/
def preNewtonState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd (MachineState.readWord mem 0) :: preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord mem
             PRE_L (preL (MachineState.readWord mem 0)))
             PRE_DODD (preDodd (MachineState.readWord mem 0)))
             PRE_X (preX (MachineState.readWord mem 0)))
             PRE_BMOD (preBmod (MachineState.readWord mem 0)) }

/-- `NEWTON_B`: the half-way Newton iterate on top. -/
def newtonBState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { preNewtonState s mem n bsize esize msize with
      pc := UInt256.ofNat pcNewtonB
      stack := newton4W (preDodd (MachineState.readWord mem 0)) ::
        preDodd (MachineState.readWord mem 0) :: preL (MachineState.readWord mem 0) ::
        MachineState.readWord mem 0 :: outer n bsize esize msize }

/-- The prologue state before storing the unrolled entry point. -/
def cacheSetupState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  kState s mem 3543 n n bsize esize msize

/-- The shift loop head with `k` steps to go. -/
def shiftLoopState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcShiftLoop k n bsize esize msize

def shiftBodyState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcShiftBody k n bsize esize msize

/-- `ESTIMATE`, with `u` already in the `t` area. -/
def estimateState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s (uMem mem n) pcEstimate k n bsize esize msize

/-- `MAC_SETUP`, with the quotient guess on top. -/
def macSetupState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcMacSetup
           stack := qhatOf (uMem mem n) :: UInt256.ofNat k :: outer n bsize esize msize
           memory := uMem mem n }

/-- The limb-pass loop head after `j` limbs, over the `u` memory `um` and guess `q`. -/
def macLoopState (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k j : Nat) :
    State :=
  { s with pc := UInt256.ofNat (pcMacLoop + 39 * ShiftUnrollEntry.cellIndex n j)
           stack := UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) j) ::
             UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j) ::
             UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 ::
             (Monpro.l1Step um q NEG n j).carry :: q :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n j).memory }

/-- The limb frame before the cached-entry dispatch. -/
def macDispatchState (s : State) (um : ByteArray) (q : UInt256)
    (n bsize esize msize k : Nat) : State :=
  { macLoopState s um q n bsize esize msize k 0 with pc := UInt256.ofNat 3679 }

/-- The middle block entry: the two spent pointers still on the stack. -/
def midState (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcMid
           stack := UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) n) ::
             UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) n) ::
             UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 ::
             (Monpro.l1Step um q NEG n n).carry :: q :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n n).memory }

/-- `ADD_LOOP` head with the current `t` memory. -/
def addLoopState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcAddLoop k n bsize esize msize

/-- `ADD_INNER` head after `j` limbs. -/
def addInnerState (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) : State :=
  { s with pc := UInt256.ofNat pcAddInner
           stack := UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j) ::
             (addStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (addStep mem n j).memory }

/-- The add tail block with the spent pointer on top. -/
def addTailState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcAddTail
           stack := UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) n) ::
             (addStep mem n n).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (addStep mem n n).memory }

def subCheckState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcSubCheck k n bsize esize msize

def subEntryState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcSubEntry k n bsize esize msize

def subInnerState (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) : State :=
  { s with pc := UInt256.ofNat pcSubInner
           stack := UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j) ::
             (subStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (subStep mem n j).memory }

def subTailState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcSubTail
           stack := UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) n) ::
             (subStep mem n n).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (subStep mem n n).memory }

def csubCallState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcCsubCall k n bsize esize msize

def afterCsubState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcAfterCsub k n bsize esize msize

def shiftDoneState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  kState s mem pcShiftDone 0 n bsize esize msize

/-- The wrapped `-32` the pointer walks add. -/
theorem negK_literal :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide


/-! ## Pointer facts used when the split loop-body blocks are composed -/

/-- One pointer step `p - 32`, as `PUSH32 -32; ADD` computes it. -/
theorem ptrAt_step (base j : Nat) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      UInt256.ofNat (Monpro.ptrAt base j) = UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod, Monpro.ptrAt_succ]

theorem negPtr_toNat (n j : Nat) (hn32 : n ≤ 32) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)).toNat = 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem negPtr_ne_zero (n j : Nat) (hn32 : n ≤ 32) (hj : j + 1 < n) :
    (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)).toNat ≠ 0 := by
  rw [negPtr_toNat n j hn32 (by omega)]; omega

theorem tPtr_toNat (n j : Nat) (hn32 : n ≤ 32) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j)).toNat = 8256 + 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem tPtr_toNat_last (n : Nat) (hn32 : n ≤ 32) :
    (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) n)).toNat = 8224 := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem tPtr_gt_8255 (n j : Nat) (hn32 : n ≤ 32) (hj : j < n) :
    8255 < (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j)).toNat := by
  rw [tPtr_toNat n j hn32 hj]; omega

theorem tPtr_gt_8224 (n j : Nat) (hn32 : n ≤ 32) (hj : j < n) :
    8224 < (UInt256.ofNat (Monpro.ptrAt (8224 + 32 * n) j)).toNat := by
  rw [tPtr_toNat n j hn32 hj]; omega

theorem aPtr_toNat (n j : Nat) (hn32 : n ≤ 32) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) j)).toNat = NEG + 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by unfold NEG; omega) (by unfold NEG; omega)]; unfold NEG; omega

end Challenge.Modexp.Submission.Proofs.Fast.Shift

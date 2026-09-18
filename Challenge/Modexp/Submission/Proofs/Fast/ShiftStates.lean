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
def pcDispatch : Nat := 2474
def pcHit : Nat := 2489
-- S1.  The recogniser miss is DIVERTED.  The old miss target (2373 in the previous
-- image) is an entry into never-executed code that this artifact deletes, so it has
-- no image under the pc map and no mechanical pass may invent one -- `fixpcconst`
-- reports it as SKIPPED-deleted-no-image for exactly that reason.  The dispatcher's
-- `PUSH2` operand at instruction 2060 now names the six-word bail trampoline
-- (`blk1351`: `JUMPDEST; PUSH1 0xee; JUMP`), which lands on the wide-modulus
-- fallback entry.  This value is TRANSCRIBED from the artifact's own immediate, not
-- derived from the divert rule: a second oracle that re-derives the rule disagreed
-- with the assembled image at four push sites, and two oracles that disagree do not
-- error, they diverge.
def pcMiss : Nat := 800

/-- The wide-modulus fallback entry `modexpBig`, where the diverted miss lands. -/
def pcBigC : Nat := 238
def pcCsubReturn : Nat := 2508
def pcAfterCsub0 : Nat := 2517
def pcNegLoop : Nat := 2523
/-- The negation body after its store, before the exit test. -/
def pcNegMid : Nat := 2539
def pcNegDone : Nat := 2549
def pcPreNewton : Nat := 2592
def pcNewtonB : Nat := 2620
def pcShiftLoop : Nat := 2691
def pcShiftBody : Nat := 2698
def pcEstimate : Nat := 2712
def pcMacSetup : Nat := 2791   -- E6, the rewritten conversion entry
def pcMid : Nat := 3093   -- the fall-through after the eight straight blocks
def pcAddLoop : Nat := 3136
def pcAddInner : Nat := 3142
def pcAddTail : Nat := 3180
/-- The add body after `OR`, before the pointer step and exit test. -/
def pcAddMid : Nat := 3167
/-- The fall-through padding after the add-round exit test. -/
def pcAddPad : Nat := 3180
def pcSubCheck : Nat := 3203
def pcSubEntry : Nat := 3215
def pcSubInner : Nat := 3221
def pcSubTail : Nat := 3260
/-- The subtract body after `OR`, before the pointer step and exit test. -/
def pcSubMid : Nat := 3245
def pcCsubCall : Nat := 3120
/-- `UNC`: the middle block's jump target when `neg ||| TN ≠ 0`. -/
def pcUnc : Nat := 3130
/-- `CSUB(BASE)` returns straight to the shift loop head (`pcShiftLoop`); the call block
already decremented the counter. -/
def pcAfterCsub : Nat := 2691
def pcShiftDone : Nat := 3274

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

/-- The dispatcher entry (pc 4076), reached from `R1B` with the outer frame. -/
def dispState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcDispatch n bsize esize msize

def hitState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcHit n bsize esize msize

def missState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcMiss n bsize esize msize

/-- Where the diverted miss lands: `modexpBig`'s entry with the outer frame intact.
The trampoline is three data-independent instructions that touch no memory and pop
only the target the `JUMP` itself pushed, so the only field that moves is `pc`. -/
def bigCState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcBigC n bsize esize msize

/-- Back from the first `CSUB`, with `BASE = b mod m`. -/
def afterCsub0State (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcAfterCsub0 n bsize esize msize

def rawCsubReturnState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcCsubReturn n bsize esize msize

/-- The negation loop head after `j` limbs: `[p, carry]` above the frame. -/
def negLoopState (s : State) (mem : ByteArray) (n bsize esize msize j : Nat) : State :=
  { s with pc := UInt256.ofNat pcNegLoop
           stack := UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j) ::
             (negStep mem n j).flag :: outer n bsize esize msize
           memory := (negStep mem n j).memory }

/-- `NEG_DONE`: all `n` limbs stored; the rotated exit test leaves the pointer already
stepped past limb `n - 1` (`2^256 - 32`) above the carry.  `blk2919` drops both. -/
def negDoneState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcNegDone
           stack := UInt256.ofNat (Monpro.ptrAt (32 * n - 32) n) :: (negStep mem n n).flag ::
             outer n bsize esize msize
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
  kState s mem 2649 n n bsize esize msize

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

/-- The middle block entry: the two spent pointers still on the stack. -/
def midState (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat) :
    State :=
  -- the eight straight blocks leave `[carry, q] ++ k :: outer` directly: the three words the old
  -- pointer loop carried, and the `POP POP POP` that discarded them, are both gone
  { s with pc := UInt256.ofNat pcMid
           stack := (Monpro.l1Step um q NEG n n).carry :: q :: UInt256.ofNat k ::
             outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n n).memory }

/-- `ADD_LOOP` head with the current `t` memory. -/
def addLoopState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcAddLoop k n bsize esize msize

/-- `ADD_INNER` head after `j` limbs. -/
def addInnerState (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) : State :=
  { s with pc := UInt256.ofNat pcAddInner
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
             (addStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (addStep mem n j).memory }

/-- The add tail block with the spent pointer on top. -/
def addTailState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcAddTail
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n) ::
             (addStep mem n n).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (addStep mem n n).memory }

def subCheckState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcSubCheck k n bsize esize msize

def subEntryState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcSubEntry k n bsize esize msize

def subInnerState (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) : State :=
  { s with pc := UInt256.ofNat pcSubInner
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
             (subStep mem n j).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (subStep mem n j).memory }

def subTailState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcSubTail
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n) ::
             (subStep mem n n).flag :: UInt256.ofNat k :: outer n bsize esize msize
           memory := (subStep mem n n).memory }

/-- The `CSUB` call block: a zero (the spent `neg`/`TN`) above the counter. -/
def csubCallState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  { s with pc := UInt256.ofNat pcCsubCall
           stack := UInt256.ofNat 0 :: UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- `UNC` with the sign flag `f` above the counter. -/
def uncState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) (f : UInt256) : State :=
  { s with pc := UInt256.ofNat pcUnc
           stack := f :: UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- `CSUB(BASE)`'s return point: the loop head with the counter already at `k - 1`. -/
def afterCsubState (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  kState s mem pcAfterCsub (k - 1) n bsize esize msize

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

theorem lnot31_eq : UInt256.lnot (31 : UInt256) =
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

/-- The rotated negation test's `PUSH1 31 NOT ADD` steps the pointer. -/
theorem negTop_succ (base j : Nat) :
    UInt256.lnot (31 : UInt256) + UInt256.ofNat (Monpro.ptrAt base j) =
      UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [lnot31_eq]; exact ptrAt_step base j

theorem negPtr_toNat (n j : Nat) (hn32 : n ≤ 8) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)).toNat = 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem negPtr_ne_zero (n j : Nat) (hn32 : n ≤ 8) (hj : j + 1 < n) :
    (UInt256.ofNat (Monpro.ptrAt (32 * n - 32) j)).toNat ≠ 0 := by
  rw [negPtr_toNat n j hn32 (by omega)]; omega

theorem tPtr_toNat (n j : Nat) (hn32 : n ≤ 8) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j)).toNat = 2112 + 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem tPtr_toNat_last (n : Nat) (hn32 : n ≤ 8) :
    (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n)).toNat = 2080 := by
  rw [Monpro.ptrAt_toNat _ _ (by omega) (by omega)]; omega

theorem tPtr_gt_8255 (n j : Nat) (hn32 : n ≤ 8) (hj : j < n) :
    2111 < (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j)).toNat := by
  rw [tPtr_toNat n j hn32 hj]; omega

theorem tPtr_gt_8224 (n j : Nat) (hn32 : n ≤ 8) (hj : j < n) :
    2080 < (UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j)).toNat := by
  rw [tPtr_toNat n j hn32 hj]; omega

theorem aPtr_toNat (n j : Nat) (hn32 : n ≤ 8) (hj : j < n) :
    (UInt256.ofNat (Monpro.ptrAt (NEG + 32 * n - 32) j)).toNat = NEG + 32 * (n - 1 - j) := by
  rw [Monpro.ptrAt_toNat _ _ (by unfold NEG; omega) (by unfold NEG; omega)]; unfold NEG; omega

end Challenge.Modexp.Submission.Proofs.Fast.Shift

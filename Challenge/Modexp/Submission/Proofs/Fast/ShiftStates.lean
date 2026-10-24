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

def pcDispatch : Nat := 2390
def pcHit : Nat := 2398
-- 3310, not ticket 4's 3282: the recogniser-miss JUMPDEST is instruction 2433 here (it was 2438),
-- and this is the one pc in the table the regenerator could not rewrite, because 3282 has no image
-- in the pc map -- R-ONE2 deleted the instruction it used to sit on, so the map row is empty and
-- the literal was left standing.  `ShiftPCs.pc2889` states instruction 2433's pc as 3310 by `rfl`,
-- and `blk2889` is located there, so a stale 3282 makes `runLocatedBlock blk2889 (missState …)`
-- return `none`.  Nothing but the build checked this def: it is a bare `Nat` with no tie to the
-- artifact, unlike every `instructionPC`/`opAt`/`pushAt` fact around it.
def pcMiss : Nat := 219
def pcBigC : Nat := 219
def pcCsubReturn : Nat := 2412
def pcAfterCsub0 : Nat := 2421
def pcNeg8 : Nat := 2429
def pcNeg4 : Nat := 2336
def pcNegT : Nat := 2470
def pcNegDone : Nat := 2494
def pcPreNewton : Nat := 2535
def pcShiftLoop : Nat := 2704
def pcShiftBody : Nat := 2705
def pcEstimate : Nat := 2719
def pcMacSetup : Nat := 2782   -- E6, the conversion entry JUMPDEST (mask already built)
def pcMid : Nat := 3034   -- the fall-through after the eight straight blocks
def pcAddLoop : Nat := 3075
def pcAddInner : Nat := 3081
def pcAddTail : Nat := 3118
def pcAddMid : Nat := 3105
def pcAddPad : Nat := 3118
def pcSubCheck : Nat := 3136
def pcCsubCall : Nat := 3061
def pcUnc : Nat := 3073
def pcAfterCsub : Nat := 2704
def pcCsubExit : Nat := 3069
def pcShiftDone : Nat := 3146

def frameState (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := mem }

def rideSlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat) (scratch : UInt256) :
    List UInt256 :=
  scratch :: MachineState.readWord mem 1312 :: MachineState.readWord mem 1344 ::
    MachineState.readWord mem 1376 :: MachineState.readWord mem 1408 ::
    MachineState.readWord mem 1440 :: MachineState.readWord mem 1472 ::
    MachineState.readWord mem 1504 :: MachineState.readWord mem 1632 ::
    MachineState.readWord mem 1664 :: MachineState.readWord mem 1568 ::
    MachineState.readWord mem 1536 :: UInt256.ofNat esize :: UInt256.ofNat n ::
    UInt256.ofNat bsize :: UInt256.ofNat 0 :: z :: []

def shiftEntry (n : Nat) : UInt256 := UInt256.ofNat (2785 + if n = 4 then 116 else 0)

def entrySlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat) : List UInt256 :=
  rideSlots z mem n bsize esize (shiftEntry n)

def slotState (z : UInt256) (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat)
    (scratch : UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := rideSlots z mem n bsize esize scratch ++ outer n bsize esize msize
           memory := mem }

def slotKState (z : UInt256) (s : State) (mem : ByteArray) (pc k : Nat)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k :: entrySlots z mem n bsize esize ++
              outer n bsize esize msize
           memory := mem }

def kState (s : State) (mem : ByteArray) (pc k : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

def dispState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcDispatch n bsize esize msize

def hitState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcHit n bsize esize msize

def missState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcMiss n bsize esize msize

def bigCState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcBigC n bsize esize msize

def afterCsub0State (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcAfterCsub0 n bsize esize msize

def rawCsubReturnState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  frameState s mem pcCsubReturn n bsize esize msize

def negState (s : State) (mem : ByteArray) (pc n bsize esize msize j : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := (negStep mem n j).memory }

def negDoneState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  negState s mem pcNegDone n bsize esize msize n

def preClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2502
           stack := preL (MachineState.readWord mem 0) :: preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := mem }

def postClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2503
           stack := UInt256.clz (preL (MachineState.readWord mem 0)) ::
             preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := mem }

def preNewtonState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd (MachineState.readWord mem 0) :: preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord mem
             PRE_X (preS (MachineState.readWord mem 0)))
             PRE_L (preK (MachineState.readWord mem 0)))
             PRE_DODD (preDodd (MachineState.readWord mem 0)))
             PRE_BMOD (preBmod (MachineState.readWord mem 0)) }

def nbHeadState (s : State) (M : ByteArray) (d : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd d :: preL d :: d :: outer n bsize esize msize
           memory := M }

def nbSubState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2543
           stack := preDodd d * n0 :: n0 :: preDodd d :: preL d :: d ::
             outer n bsize esize msize
           memory := M }

def nbTailState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2594
           stack := newton8W (preDodd d * n0) :: n0 :: preDodd d :: preL d :: d ::
             outer n bsize esize msize
           memory := M }

def nbOutMem (M : ByteArray) (d n0 : UInt256) : ByteArray :=
  Exp.storeWord (Exp.storeWord M PRE_DINV (newton8W (preDodd d * n0) * n0)) 2720
    (UInt256.ofNat 0 - preDodd d * newton8W (preDodd d * n0))

def cacheSetupState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  slotState (UInt256.ofNat 0) s mem 2663 n bsize esize msize (UInt256.ofNat n)

def shiftLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcShiftLoop k n bsize esize msize

def shiftBodyState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcShiftBody k n bsize esize msize

def estimateState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  slotKState z s (uMem mem n) pcEstimate k n bsize esize msize

def macSetupState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcMacSetup
           stack := qhatOf (uMem mem n) :: Monpro.maxWord :: UInt256.ofNat k :: entrySlots z (uMem mem n) n bsize esize ++
             outer n bsize esize msize
           memory := uMem mem n }

def midState (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcMid
           stack := (Monpro.l1Step um q NEG n n).carry :: q :: Monpro.maxWord :: UInt256.ofNat k ::
             entrySlots z um n bsize esize ++ outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n n).memory }

def addLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcAddLoop k n bsize esize msize

def addInnerState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddInner
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
             (addStep mem n j).flag :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := (addStep mem n j).memory }

def addTailState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddTail
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n) ::
             (addStep mem n n).flag :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := (addStep mem n n).memory }

def subCheckState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcSubCheck k n bsize esize msize

def csubCallState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcCsubCall
           stack := UInt256.ofNat 0 :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }

def uncState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (f : UInt256) : State :=
  { s with pc := UInt256.ofNat pcUnc
           stack := f :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }

def afterCsubState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  slotKState z s mem pcAfterCsub (k - 1) n bsize esize msize

def csubExitState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcCsubExit 0 n bsize esize msize

def shiftDoneState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcShiftDone 0 n bsize esize msize

def cleanupState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotState z s mem 5522 n bsize esize msize (shiftEntry n)

theorem negK_literal :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 :
      UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide


/-! ## Pointer facts used when the split loop-body blocks are composed -/

theorem ptrAt_step (base j : Nat) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      UInt256.ofNat (Monpro.ptrAt base j) = UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod, Monpro.ptrAt_succ]

theorem lnot31_eq : UInt256.lnot (31 : UInt256) =
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide

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

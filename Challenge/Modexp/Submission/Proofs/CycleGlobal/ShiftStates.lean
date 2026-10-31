import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel

noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Block-boundary states of the shift-reduce base conversion

Every state is stated over an arbitrary carrier `s` and overrides only `pc`,
`stack` and `memory`.  The outer frame `outer n bsize esize msize` sits at the
bottom throughout.
-/

namespace CycleSubmission.Global.Fast.Shift
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Shift


open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

abbrev outer := Exp.outer

/-- Program counters of the appended routine. -/
def pcDispatch : Nat := 2390
def pcHit : Nat := 2398
-- 3310, not ticket 4's 3282: the recogniser-miss JUMPDEST is instruction 2433 here (it was 2438),
-- and this is the one pc in the table the regenerator could not rewrite, because 3282 has no image
-- in the pc map -- R-ONE2 deleted the instruction it used to sit on, so the map row is empty and
-- the literal was left standing.  `ShiftPCs.pc2889` states instruction 2433's pc as 3310 by `rfl`,
-- and `blk2889` is located there, so a stale 3282 makes `runLocatedBlock blk2889 (missState …)`
-- return `none`.  Nothing but the build checked this def: it is a bare `Nat` with no tie to the
-- artifact, unlike every `instructionPC`/`opAt`/`pushAt` fact around it.
/-- The full-base miss no longer seeds `R1` and converts: the dispatcher's `JUMPI`
names the six-word bail trampoline (`BAIL6`, pc 1054), which lands on `modexpBig`. -/
def pcMiss : Nat := 219
/-- `modexpBig`, where the trampoline lands. -/
def pcBigC : Nat := 219
def pcCsubReturn : Nat := 2412
def pcAfterCsub0 : Nat := 2421
/-- The eight-limb negation cells (the width test's fall-through). -/
def pcNeg8 : Nat := 2429
/-- The four-limb negation stub. -/
def pcNeg4 : Nat := 2336
/-- `NEG_TAIL`, the cells both widths share. -/
def pcNegT : Nat := 2470
/-- `NEG_DONE`: all `n` limbs of `NEG` stored. -/
def pcNegDone : Nat := 2494
def pcPreNewton : Nat := 2535
def pcShiftLoop : Nat := 2714
def pcShiftBody : Nat := 2709
def pcEstimate : Nat := 2723
def pcMacSetup : Nat := 2787   -- block 0's first product: E6 and block 0's `JUMPDEST POP` are gone
/-- The loop head of the width: the eight-limb head falls straight into block 0 at 2787; the
four-limb head is a copy appended at 10754 that ends in `PUSH0 PUSH2 2901 JUMP` (block 4). -/
def headPC (n : Nat) : Nat := if n = 4 then 10754 else 2714
/-- The scratch slot: the loop head of the width, the target of the bottom test and of the
E3 phase switch. -/
def headWord (n : Nat) : UInt256 := UInt256.ofNat (headPC n)
def pcMid : Nat := 3034   -- the fall-through after the eight straight blocks
/-- The middle block of the width: the four-limb loop runs a private copy appended at 10945. -/
def midPC (n : Nat) : Nat := if n = 4 then 10945 else 3034
def pcAddLoop : Nat := 3106
def pcAddInner : Nat := 3112
def pcAddTail : Nat := 3149
/-- The add body after `OR`, before the pointer step and exit test. -/
def pcAddMid : Nat := 3136
/-- The fall-through padding after the add-round exit test. -/
def pcAddPad : Nat := 3149
def pcSubCheck : Nat := 3167
def pcCsubCall : Nat := 3063
/-- `UNC`: the middle block's jump target when `neg ||| TN ≠ 0`. -/
def pcUnc : Nat := 3104
/-- `CSUB(BASE)` returns straight to the shift loop head (`pcShiftLoop`); the call block
already decremented the counter. -/
def pcAfterCsub : Nat := 2714
/-- The loop exit after the last step (`PUSH2 3366 JUMP`, the `JUMPI` fall-through). -/
def pcCsubExit : Nat := 3069
def pcShiftDone : Nat := 3069

/-- A state with the outer frame only. -/
def frameState (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := mem }

/-- The seventeen words the ported prologue parks on the stack through the shift
window, top word first: the scratch slot, eleven frame words read from
`0x520`-`0x680`, then `esize`, `n`, `bsize`, a zero and the exit slot `z`, all above
the outer frame.  Every word but the scratch slot is immutable through each loop.
`E5` parks `z = 0`; the E3 phase switch sets `z = 30`.  The cleanup tail jumps to
`2441 + z`: the exponent dispatcher, or `e3go` (2471) after the E3 conversion. -/
def rideSlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat) (scratch : UInt256) :
    List UInt256 :=
  scratch :: MachineState.readWord mem 1312 :: MachineState.readWord mem 1344 ::
    MachineState.readWord mem 1376 :: MachineState.readWord mem 1408 ::
    MachineState.readWord mem 1440 :: MachineState.readWord mem 1472 ::
    MachineState.readWord mem 1504 :: MachineState.readWord mem 1632 ::
    MachineState.readWord mem 1664 :: MachineState.readWord mem 1568 ::
    MachineState.readWord mem 1536 :: UInt256.ofNat esize :: UInt256.ofNat n ::
    UInt256.ofNat bsize :: UInt256.ofNat 0 :: z :: []

/-- The unrolled-conversion entry the cache block stores at `0x6a2` and parks in
the scratch slot for the rest of the window: `2940 + 116 · [n = 4]`. -/
def shiftEntry (n : Nat) : UInt256 := UInt256.ofNat (2785 + if n = 4 then 116 else 0)

/-- The window's riding slots with the scratch slot holding the conversion entry. -/
def entrySlots (z : UInt256) (mem : ByteArray) (n bsize _esize : Nat) : List UInt256 :=
  headWord n :: MachineState.readWord mem 1312 :: MachineState.readWord mem 1344 ::
    MachineState.readWord mem 1376 :: MachineState.readWord mem 1408 ::
    MachineState.readWord mem 1440 :: MachineState.readWord mem 1472 ::
    MachineState.readWord mem 1504 :: MachineState.readWord mem 1632 ::
    MachineState.readWord mem 1664 :: MachineState.readWord mem 1568 ::
    MachineState.readWord mem 1536 ::
    UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128) :: UInt256.ofNat n ::
    UInt256.ofNat bsize :: UInt256.ofNat 0 :: z :: []

/-- A state inside the riding window: the slots above the outer frame. -/
def slotState (z : UInt256) (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat)
    (scratch : UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := rideSlots z mem n bsize esize scratch ++ outer n bsize esize msize
           memory := mem }

/-- A state with the loop counter above the riding slots. -/
def slotKState (z : UInt256) (s : State) (mem : ByteArray) (pc k : Nat)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k :: entrySlots z mem n bsize esize ++
              outer n bsize esize msize
           memory := mem }

/-- A state with one counter word above the outer frame. -/
def kState (s : State) (mem : ByteArray) (pc k : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k :: outer n bsize esize msize
           memory := mem }

/-- The dispatcher entry (pc 3587), reached from `R1B` with the outer frame. -/
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

/-- A state of the straight-line negation (negun): the outer frame only, `NEG` written
through limb `j` (`negStep mem n j`). -/
def negState (s : State) (mem : ByteArray) (pc n bsize esize msize j : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := (negStep mem n j).memory }

/-- `NEG_DONE`: all `n` limbs stored, the outer frame only. -/
def negDoneState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  negState s mem pcNegDone n bsize esize msize n

/-- The estimator prologue's `CLZ` (pc 2672, CLZ cut): `[L, L, d]` above the frame. -/
def preClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2502
           stack := preL (MachineState.readWord mem 0) :: preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := mem }

/-- Just after the `CLZ` (pc 2673): `[clz L, L, d]` above the frame. -/
def postClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2503
           stack := UInt256.clz (preL (MachineState.readWord mem 0)) ::
             preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := mem }

/-- `PRE_NEWTON`: `[dodd, d]` above the frame (the spare `L` copy is no longer kept), four words stored (CLZ cut: the shift
words `PRE_X := preS d` and `PRE_L := preK d` first). -/
def preNewtonState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0 :: outer n bsize esize msize
           memory := Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord mem
             PRE_X (preS (MachineState.readWord mem 0)))
             PRE_L (preK (MachineState.readWord mem 0)))
             PRE_DODD (preDodd (MachineState.readWord mem 0)))
             PRE_BMOD (preBmod (MachineState.readWord mem 0)) }

/-- The newton-batch head (pc 2705) over a raw memory `M`, with the top limb `d`. -/
def nbHeadState (s : State) (M : ByteArray) (d : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd d :: d :: outer n bsize esize msize
           memory := M }

/-- The shared Newton chain entry (pc 714): `dodd * n0` and the return pc 2741 on top. -/
def nbSubState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2543
           stack := preDodd d * n0 :: n0 :: preDodd d :: d ::
             outer n bsize esize msize
           memory := M }

/-- The newton-batch tail (pc 2741): the inverse of `dodd * n0` on top. -/
def nbTailState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2594
           stack := newton8W (preDodd d * n0) :: n0 :: preDodd d :: d ::
             outer n bsize esize msize
           memory := M }

/-- The memory the newton-batch tail leaves: `dinv := x * n0` and `V_MINV := -(dodd * x)`. -/
def nbOutMem (M : ByteArray) (d n0 : UInt256) : ByteArray :=
  Exp.storeWord (Exp.storeWord M PRE_DINV (newton8W (preDodd d * n0) * n0)) 2720
    (UInt256.ofNat 0 - preDodd d * newton8W (preDodd d * n0))

/-- The cache-setup entry (`E5`, pc 2764): the prologue has just parked the riding
slots with the outer `n` in the scratch position. -/
def cacheSetupState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  slotState (UInt256.ofNat 0) s mem 2663 n bsize esize msize (UInt256.ofNat n)

/-- The shift loop head with `k` steps to go. -/
def shiftLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem (headPC n) k n bsize esize msize

def shiftBodyState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem (headPC n + 1) k n bsize esize msize

/-- `ESTIMATE`, with `u` already in the `t` area. -/
def estimateState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  slotKState z s (uMem mem n) (headPC n + 14) k n bsize esize msize

/-- `MAC_SETUP`, with the quotient guess on top of the `2^256-1` mask. -/
def macSetupState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat (headPC n + 73)
           stack := qhatOf (uMem mem n) :: Monpro.maxWord :: UInt256.ofNat k :: entrySlots z (uMem mem n) n bsize esize ++
             outer n bsize esize msize
           memory := uMem mem n }

/-- The middle block entry: the eight straight blocks leave `[carry, q, 2^256-1]` above the
counter and the riding slots.  The mask survives pc 3168..3170 (three `JUMPDEST`s) and is spent
by `SWAP3 POP` at pc 3184..3185, so it is still in its slot here; every state from pc 3186 on
has the `[carry, q]` shape the block used to start from. -/
def midState (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat (midPC n)
           stack := (Monpro.l1Step um q NEG n n).carry :: q :: Monpro.maxWord :: UInt256.ofNat k ::
             entrySlots z um n bsize esize ++ outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n n).memory }

/-- `ADD_LOOP` head with the current `t` memory. -/
def addLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcAddLoop k n bsize esize msize

/-- `ADD_INNER` head after `j` limbs. -/
def addInnerState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddInner
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
             (addStep mem n j).flag :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := (addStep mem n j).memory }

/-- The add tail block with the spent pointer on top. -/
def addTailState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddTail
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n) ::
             (addStep mem n n).flag :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := (addStep mem n n).memory }

def subCheckState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcSubCheck k n bsize esize msize

/-- The `CSUB` call block: a zero (the spent `neg`/`TN`) above the counter. -/
def csubCallState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcCsubCall
           stack := UInt256.ofNat 0 :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }


/-- The four-limb private counter block (pc 10974, no `JUMPDEST`). -/
def csubCall4State (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat 10974
           stack := UInt256.ofNat 0 :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }

/-- `UNC` with the sign flag `f` above the counter. -/
def uncState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (f : UInt256) : State :=
  { s with pc := UInt256.ofNat pcUnc
           stack := f :: UInt256.ofNat k ::
             entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }

/-- `CSUB(BASE)`'s return point: the loop head with the counter already at `k - 1`. -/
def afterCsubState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  slotKState z s mem (headPC n) (k - 1) n bsize esize msize

/-- The bottom `JUMPI` fell through: the counter reached zero. -/
def csubExitState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcCsubExit 0 n bsize esize msize


/-- The four-limb counter fell through (pc 10979, `PUSH2 3069 JUMP`). -/
def csubExit4State (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem 10979 0 n bsize esize msize

/-- The loop exit with the spent counter still on top of the slots. -/
def shiftDoneState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcShiftDone 0 n bsize esize msize

/-- The cleanup tail (pc 3866): the spent counter is gone; sixteen `POP`s drop all
riding slots but the exit slot `z`, which picks the jump target `2441 + z`. -/
def cleanupState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  { s with pc := UInt256.ofNat 3944
           stack := entrySlots z mem n bsize esize ++ outer n bsize esize msize
           memory := mem }

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

end CycleSubmission.Global.Fast.Shift

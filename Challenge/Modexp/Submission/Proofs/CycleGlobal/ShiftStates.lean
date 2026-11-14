import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ZeroShiftMath
noncomputable section
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
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
def pcDispatch : Nat := 660
def pcHit : Nat := 667
-- 3316, not ticket 4's 3288: the recogniser-miss JUMPDEST is instruction 2439 here (it was 2444),
-- and this is the one pc in the table the regenerator could not rewrite, because 3288 has no image
-- in the pc map -- R-ONE2 deleted the instruction it used to sit on, so the map row is empty and
-- the literal was left standing.  `ShiftPCs.pc2889` states instruction 2439's pc as 3316 by `rfl`,
-- and `blk2889` is located there, so a stale 3288 makes `runLocatedBlock blk2889 (missState …)`
-- return `none`.  Nothing but the build checked this def: it is a bare `Nat` with no tie to the
-- artifact, unlike every `instructionPC`/`opAt`/`pushAt` fact around it.
def pcMiss : Nat := 207
def pcBigC : Nat := 207
def pcCsubReturn : Nat := 2566
def pcAfterCsub0 : Nat := 2575
def pcNeg8 : Nat := 2583
def pcNeg4 : Nat := 2513
def pcNegT : Nat := 2624
def pcNegDone : Nat := 2649
def pcPreNewton : Nat := 2686
def pcShiftLoop : Nat := 2874
def pcShiftBody : Nat := 2875
def pcEstimate : Nat := 2883
def pcMacSetup : Nat := 2941   -- block 0's first product: E6 and block 0's `JUMPDEST POP` are gone
def headPC (n : Nat) : Nat := if n = 4 then 10618 else 2874
def loopPC (mem : ByteArray) (n : Nat) : Nat :=
  CycleSubmission.Global.ZeroShiftMath.head n (MachineState.readWord mem 1536)
def headWord (mem : ByteArray) (n : Nat) : UInt256 := UInt256.ofNat (loopPC mem n)
theorem loopPC_lt (mem : ByteArray) (n : Nat) : loopPC mem n < 2^256 := by
  unfold loopPC CycleSubmission.Global.ZeroShiftMath.head
    CycleSubmission.Global.ZeroShiftMath.normalHead CycleSubmission.Global.ZeroShiftMath.zeroHead
  split_ifs <;> norm_num
@[simp] theorem loopPC_eq (mem : ByteArray) (n : Nat)
    (hk : (MachineState.readWord mem 1536).toNat ≠ 0) : loopPC mem n = headPC n := by
  simp [loopPC,CycleSubmission.Global.ZeroShiftMath.head,
    CycleSubmission.Global.ZeroShiftMath.normalHead,headPC,hk]
def pcMid : Nat := 3187   -- the fall-through after the eight straight blocks
def midPC (n : Nat) : Nat := if n = 4 then 10803 else 3187
def pcAddLoop : Nat := 3215
def pcAddInner : Nat := 3221
def pcAddTail : Nat := 3258
def pcAddMid : Nat := 3245
def pcAddPad : Nat := 3258
def pcSubCheck : Nat := 3276
def pcCsubCall : Nat := 3200
def pcUnc : Nat := 3214
def pcAfterCsub : Nat := 2840
def pcCsubExit : Nat := 3206
def pcShiftDone : Nat := 3206
def frameState (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := outer n bsize esize msize
           memory := mem }
/- Conversion states carry their actual continuation as z. -/
def rideSlots (z : UInt256) (mem : ByteArray) (n bsize esize : Nat) (scratch : UInt256) :
    List UInt256 :=
  scratch::MachineState.readWord mem 1312::MachineState.readWord mem 1344 ::
    MachineState.readWord mem 1376::MachineState.readWord mem 1408 ::
    MachineState.readWord mem 1440::MachineState.readWord mem 1472 ::
    MachineState.readWord mem 1504::MachineState.readWord mem 1632 ::
    MachineState.readWord mem 1664::MachineState.readWord mem 1568 ::
    MachineState.readWord mem 1536::UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128) ::
    z::[]
def shiftEntry (n : Nat) : UInt256 := UInt256.ofNat (2739 + if n = 4 then 116 else 0)
def aprevSlot (mem : ByteArray) : UInt256 := MachineState.readWord mem 1536
def hdSlot (mem : ByteArray) : UInt256 := UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128)
def entrySlots (z : UInt256) (mem : ByteArray) (n bsize _esize : Nat) : List UInt256 :=
  headWord mem n::MachineState.readWord mem 1312::MachineState.readWord mem 1344 ::
    MachineState.readWord mem 1376::MachineState.readWord mem 1408 ::
    MachineState.readWord mem 1440::MachineState.readWord mem 1472 ::
    MachineState.readWord mem 1504::MachineState.readWord mem 1632 ::
    MachineState.readWord mem 1664::MachineState.readWord mem 1568 ::
    aprevSlot mem::hdSlot mem ::
    z::[]
def slotState (z : UInt256) (s : State) (mem : ByteArray) (pc : Nat) (n bsize esize msize : Nat)
    (scratch : UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := rideSlots z mem n bsize esize scratch++outer n bsize esize msize
           memory := mem }
def slotKState (z : UInt256) (s : State) (mem : ByteArray) (pc k : Nat)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k::entrySlots z mem n bsize esize ++
              outer n bsize esize msize
           memory := mem }
def kState (s : State) (mem : ByteArray) (pc k : Nat) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pc
           stack := UInt256.ofNat k::outer n bsize esize msize
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
  { negState s mem pcNegDone n bsize esize msize n with
    stack := MachineState.readWord (negStep mem n n).memory 0::outer n bsize esize msize }
def preClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2654
           stack := preL (MachineState.readWord mem 0) ::
             MachineState.readWord mem 0::outer n bsize esize msize
           memory := mem }
def postClzState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2655
           stack := UInt256.clz (preL (MachineState.readWord mem 0)) ::
             MachineState.readWord mem 0::outer n bsize esize msize
           memory := mem }
def preNewtonState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd (MachineState.readWord mem 0) ::
             outer n bsize esize msize
           memory := Exp.storeWord (Exp.storeWord (Exp.storeWord (Exp.storeWord mem
             PRE_X (preS (MachineState.readWord mem 0)))
             PRE_L (preK (MachineState.readWord mem 0)))
             PRE_DODD (preDodd (MachineState.readWord mem 0)))
             PRE_BMOD (preBmod (MachineState.readWord mem 0)) }
def nbHeadState (s : State) (M : ByteArray) (d : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat pcPreNewton
           stack := preDodd d::outer n bsize esize msize
           memory := M }
def nbSubState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2694
           stack := preDodd d * n0::n0::preDodd d ::
             outer n bsize esize msize
           memory := M }
def nbTailState (s : State) (M : ByteArray) (d n0 : UInt256) (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2743
           stack := newton8W (preDodd d * n0)::n0::preDodd d ::
             outer n bsize esize msize
           memory := M }
def nbOutMem (M : ByteArray) (d n0 : UInt256) : ByteArray :=
  Exp.storeWord (Exp.storeWord M PRE_DINV (newton8W (preDodd d * n0) * n0)) 2720
    (UInt256.ofNat 0 - preDodd d * newton8W (preDodd d * n0))
def initialPhase (s : State) (mem : ByteArray) (esize : Nat) : UInt256 :=
  UInt256.land
    (UInt256.eq (UInt256.ofNat 3) (UInt256.byteAt (UInt256.ofNat 0)
      (MachineState.readWord s.executionEnv.calldata (MachineState.readWord mem 2656).toNat)))
    (UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat esize))
def initialContinuation (s : State) (mem : ByteArray) (esize : Nat) : UInt256 :=
  UInt256.ofNat 2534 + initialPhase s mem esize * UInt256.ofNat 7783
def cacheSetupState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
  slotState (initialContinuation s mem esize) s mem 2835 n bsize esize msize
    (UInt256.ofNat n)
def shiftLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem (loopPC mem n) k n bsize esize msize
def shiftBodyState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem (headPC n + 1) k n bsize esize msize
def uMem0 (mem : ByteArray) (n : Nat) : ByteArray := Exp.mcopyMem mem 2080 2112 (32 * n)
theorem uMem_eq_store (mem : ByteArray) (n : Nat) :
    uMem mem n = Exp.storeWord (uMem0 mem n) (2080 + 32 * n) (UInt256.ofNat 0) := rfl
theorem uMem0_readWord (mem : ByteArray) (n a : Nat) (ha : a + 32 ≤ 2080 + 32 * n) :
    MachineState.readWord (uMem0 mem n) a = MachineState.readWord (uMem mem n) a := by
  rw [uMem_eq_store]
  exact (Exp.storeWord_readWord_disjoint (uMem0 mem n) (2080 + 32 * n) a _ (Or.inl ha)).symm
def estimateState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { slotKState z s (uMem mem n) ((headPC n + 9)) k n bsize esize msize with memory := uMem0 mem n }
def macSetupState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat ((headPC n + 67))
           stack := qhatOf (uMem mem n)::Monpro.maxWord::UInt256.ofNat k::entrySlots z (uMem mem n) n bsize esize ++
             outer n bsize esize msize
           memory := uMem0 mem n }
def midState (z : UInt256) (s : State) (um : ByteArray) (q : UInt256) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat (midPC n)
           stack := (Monpro.l1Step um q NEG n n).carry::q::Monpro.maxWord::UInt256.ofNat k ::
             entrySlots z um n bsize esize++outer n bsize esize msize
           memory := (Monpro.l1Step um q NEG n n).memory }
def addLoopState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcAddLoop k n bsize esize msize
def addInnerState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k j : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddInner
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) j) ::
             (addStep mem n j).flag::UInt256.ofNat k ::
             entrySlots z mem n bsize esize++outer n bsize esize msize
           memory := (addStep mem n j).memory }
def addTailState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcAddTail
           stack := UInt256.ofNat (Monpro.ptrAt (2080 + 32 * n) n) ::
             (addStep mem n n).flag::UInt256.ofNat k ::
             entrySlots z mem n bsize esize++outer n bsize esize msize
           memory := (addStep mem n n).memory }
def subCheckState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
  slotKState z s mem pcSubCheck k n bsize esize msize
def csubCallState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat pcCsubCall
           stack := UInt256.ofNat 0::UInt256.ofNat k ::
             entrySlots z mem n bsize esize++outer n bsize esize msize
           memory := mem }
def csubCall4State (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  { s with pc := UInt256.ofNat 10816
           stack := UInt256.ofNat 0::UInt256.ofNat k ::
             entrySlots z mem n bsize esize++outer n bsize esize msize
           memory := mem }
def uncState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
    (f : UInt256) : State :=
  { s with pc := UInt256.ofNat pcUnc
           stack := f::UInt256.ofNat k ::
             entrySlots z mem n bsize esize++outer n bsize esize msize
           memory := mem }
def afterCsubState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) :
    State :=
  slotKState z s mem (loopPC mem n) (k - 1) n bsize esize msize
def csubExitState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcCsubExit 0 n bsize esize msize
def csubExit4State (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem 10821 0 n bsize esize msize
def shiftDoneState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
    State :=
  slotKState z s mem pcShiftDone 0 n bsize esize msize
theorem negK_literal :
    (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) = UInt256.ofNat
        115792089237316195423570985008687907853269984665640564039457584007913129639904 := by
  decide
theorem ptrAt_step (base j : Nat) :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 +
      UInt256.ofNat (Monpro.ptrAt base j) = UInt256.ofNat (Monpro.ptrAt base (j + 1)) := by
  rw [Challenge.EvmProof.Word.ofNat_add_mod,Monpro.ptrAt_succ]
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
end CycleSubmission.Global.Fast.Shift

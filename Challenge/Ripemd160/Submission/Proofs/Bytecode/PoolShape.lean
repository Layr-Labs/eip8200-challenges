import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolRawWriter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

/-- Bytes that the next block's overlapping loads require to be zero. -/
def zeroAddresses : List Nat :=
  0 :: ((List.range 14).map (· + 14) ++ [60,61,594,595,614,615,648,649] ++
    PairStoreGap.lowerPairSlots.flatMap (fun j => (List.range 4).map (fun k => 18*j+14+k)))

def Clear (memory : ByteArray) : Prop :=
  ∀ a, a ∈ zeroAddresses → memory[a]?.getD 0 = 0

inductive Source where
  | zero
  | memory (a : Nat)
  | low (i : Nat)
  | high (i : Nat)
  | join (a b : Source)
  deriving DecidableEq

def Source.eval (memory : ByteArray) (low high : UInt256) : Source → UInt8
  | .zero => 0
  | .memory a => memory[a]?.getD 0
  | .low i => PoolByte.byte low i
  | .high i => PoolByte.byte high i
  | .join a b => a.eval memory low high ||| b.eval memory low high

def join : Source → Source → Source
  | .zero, b => b
  | a, .zero => a
  | a, b => .join a b

theorem eval_join (m : ByteArray) (lo hi : UInt256) (a b : Source) :
    (join a b).eval m lo hi = a.eval m lo hi ||| b.eval m lo hi := by
  cases a <;> cases b <;> simp [join, Source.eval]

def incoming (a : Nat) : Source := if a ∈ zeroAddresses then .zero else .memory a

theorem eval_incoming (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    m[a]?.getD 0 = (incoming a).eval m lo hi := by
  unfold incoming
  split
  · exact hc a ‹_›
  · rfl

def scratchSource (a : Nat) : Source :=
  if 28 ≤ a ∧ a < 60 then .low (a-28)
  else if 10 ≤ a ∧ a < 28 then .low (a-10)
  else if 60 ≤ a ∧ a < 78 then .low (a-46)
  else if 96 ≤ a ∧ a < 128 then .high (a-96)
  else incoming a

def copiedAddress (a : Nat) : Nat :=
  if 130 ≤ a ∧ a < 146 then a-18
  else if 78 ≤ a ∧ a < 94 then a+18 else a

def fanSource (a : Nat) : Source := scratchSource (copiedAddress a)

theorem scratch_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    (Pair13Endian.scratch3 m lo hi)[a]?.getD 0 = (scratchSource a).eval m lo hi := by
  rw [Shared32Scratch.scratch3_getD]
  unfold scratchSource
  split_ifs <;> simp (discharger := omega) only [Source.eval, PoolByte.encoded, eval_incoming m lo hi hc]

theorem fan_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m) (a : Nat) :
    (Shared32Scratch.fanMemory m lo hi)[a]?.getD 0 = (fanSource a).eval m lo hi := by
  rw [Shared32Scratch.fanMemory, Shared32Scratch.copied_getD]
  unfold fanSource copiedAddress
  split_ifs <;> exact scratch_shape m lo hi hc _

def laneByte (j : Nat) : Prop := (10 ≤ j ∧ j < 14) ∨ (28 ≤ j ∧ j < 32)
instance (j : Nat) : Decidable (laneByte j) := inferInstanceAs (Decidable (_ ∨ _))

def maskSource (j : Nat) (x : Source) : Source := if laneByte j then x else .zero

theorem byte_mask (x : UInt256) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.land Pair13PoolRaw.poolMask x) j =
      if laneByte j then PoolByte.byte x j else 0 := by
  have hm : ∀ i : Fin 32, PoolByte.byte Pair13PoolRaw.poolMask i.val =
      if laneByte i.val then 255 else 0 := by decide
  rw [PoolByte.land, hm ⟨j,hj⟩]
  split
  · apply UInt8.eq_of_toBitVec_eq
    exact BitVec.allOnes_and
  · apply UInt8.eq_of_toBitVec_eq
    exact BitVec.zero_and

def loadSource (i j : Nat) : Source := fanSource (Pair13PoolRaw.poolAddr i+j)

/-- Since the four masks at m0..m3 the masked set is the complement of the seven unmasked
sources, i.e. exactly the measured junk-free set {0,1,2,3,4,5,6,7,11}; the `i = 3` join
disappeared with its `DUP1; SHL 144; OR` doubling. -/
def poolSource (clean : Bool) (i j : Nat) : Source :=
  if clean || decide (i ∈ [0,1,2,3,4,5,6,7,11]) then maskSource j (loadSource i j)
  else loadSource i j

def poolValue (clean : Bool) (m : ByteArray) : Nat → UInt256 :=
  if clean then Pair13PoolRaw.cleanPoolWord m else Pair13PoolRaw.poolWord m

theorem pool_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m)
    (clean : Bool) (i j : Nat) (hi16 : i < 16) (hj : j < 32) :
    PoolByte.byte (poolValue clean (Shared32Scratch.fanMemory m lo hi) i) j =
      (poolSource clean i j).eval m lo hi := by
  have hr (i j : Nat) (hj : j < 32) :
      PoolByte.byte (Pair13PoolRaw.rawLoad (Shared32Scratch.fanMemory m lo hi) i) j =
        (loadSource i j).eval m lo hi := by
    rw [Pair13PoolRaw.rawLoad, PoolByte.read _ _ _ hj, fan_shape m lo hi hc]
    rfl
  cases clean <;> interval_cases i <;> interval_cases j <;>
    simp (config := { maxSteps := 200000 }) (discharger := omega) [poolValue, poolSource, Pair13PoolRaw.poolWord,
      Pair13PoolRaw.cleanPoolWord, PoolByte.lor, PoolByte.shl144,
      byte_mask, hr, maskSource, laneByte, eval_join, Source.eval]

def writes : List (Nat × Nat) :=  [ (126,11),
    (900,9),
    (216,10),
    (882,3),
    (864,11),
    (846,3),
    (828,9),
    (558,8),
    (684,6),
    (936,8),
    (108,5),
    (792,1),
    (540,1),
    (756,9),
    (522,0),
    (90,12),
    (72,4),
    (54,0),
    (666,14),
    (504,1),
    (1080,5),
    (1062,13),
    (486,5),
    (972,3),
    (648,15),
    (1008,15),
    (630,10),
    (612,15),
    (738,8),
    (288,7),
    (594,11),
    (1044,6),
    (414,6),
    (720,5),
    (270,15),
    (396,4),
    (468,1),
    (18,4),
    (360,2),
    (198,13),
    (324,10),
    (252,7),
    (0,6),
    (450,12),
    (162,14) ]

theorem rawWrites_eq (words : Nat → UInt256) :
    PoolRawWriter.rawWrites words = writes.map (fun x => (x.1,words x.2)) := rfl

def storeSource (f : Nat → Source) (g : Nat → Nat → Source) (a i p : Nat) : Source :=
  if a ≤ p ∧ p < a+32 then g i (p-a) else f p

def storeSources (g : Nat → Nat → Source) : (Nat → Source) → List (Nat × Nat) → (Nat → Source)
  | f, [] => f
  | f, (a,i)::rest => storeSources g (storeSource f g a i) rest

theorem writeChain_shape (m original : ByteArray) (lo hi : UInt256)
    (f : Nat → Source) (words : Nat → UInt256) (g : Nat → Nat → Source)
    (ws : List (Nat × Nat))
    (hf : ∀ a, m[a]?.getD 0 = (f a).eval original lo hi)
    (hg : ∀ x ∈ ws, ∀ j, j < 32 → PoolByte.byte (words x.2) j = (g x.2 j).eval original lo hi) :
    ∀ a, (Pair13WriterRaw.writeChain m (ws.map (fun x => (x.1,words x.2))))[a]?.getD 0 =
      (storeSources g f ws a).eval original lo hi := by
  induction ws generalizing m f with
  | nil => exact hf
  | cons x rest ih =>
    rcases x with ⟨address,index⟩
    simp only [List.map_cons, Pair13WriterRaw.writeChain_cons, storeSources]
    apply ih
    · intro a
      rw [Shared32Scratch.writeWord_getD]
      unfold storeSource
      by_cases ha : address ≤ a ∧ a < address+32
      · rw [if_pos ha, if_pos ha, PoolByte.encoded _ _ (by omega),
          hg (address,index) (List.mem_cons_self ..) _ (by omega)]
      · rw [if_neg ha, if_neg ha]
        exact hf a
    · intro x hx j hj
      exact hg x (List.mem_cons_of_mem _ hx) j hj

def resultSource (clean : Bool) : Nat → Source := storeSources (poolSource clean) fanSource writes

def resultMemory (clean : Bool) (m : ByteArray) (lo hi : UInt256) : ByteArray :=
  PoolRawWriter.writerMemory (Shared32Scratch.fanMemory m lo hi)
    (poolValue clean (Shared32Scratch.fanMemory m lo hi))

theorem result_shape (m : ByteArray) (lo hi : UInt256) (hc : Clear m)
    (clean : Bool) (a : Nat) :
    (resultMemory clean m lo hi)[a]?.getD 0 = (resultSource clean a).eval m lo hi := by
  rw [resultMemory, PoolRawWriter.writerMemory, rawWrites_eq]
  have hindices : ∀ x ∈ writes, x.2 < 16 := by decide
  exact writeChain_shape _ m lo hi _ _ _ writes (fan_shape m lo hi hc)
    (fun x hx j hj => pool_shape m lo hi hc clean x.2 j (hindices x hx) hj) a

#print axioms pool_shape
#print axioms result_shape
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape

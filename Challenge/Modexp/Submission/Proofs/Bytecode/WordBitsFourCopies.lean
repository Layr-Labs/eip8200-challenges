import Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFour
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCopies
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WordStep WordBitsFour WordBitsFourCore

def value (j : Nat) (Bm1 byte acc m : UInt256) : UInt256 :=
  UInt256.mulMod (UInt256.mulMod acc acc m)
    (1 + Bm1 * UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7-j))) 1) m

variable (s : State) (rest : List UInt256)
  (Bm1 byte offset outerW acc base m : UInt256) (hs : Frame s) (hrest : rest.length < 1000)

def gasSteps_copy0 :
    GasSteps (stW s 2510 ([Bm1,0,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2533 ([Bm1,0,byte,offset,outerW,(value 0 Bm1 byte acc m),base,m] ++ rest)) := by
  refine ((start s rest Bm1 byte offset outerW acc base m hs hrest 0).trans (body0 s rest Bm1 byte offset outerW acc base m hs hrest 0)).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 7 - UInt256.ofNat 0 = UInt256.ofNat 7 from by decide]

@[simp] theorem gasSteps_copy0_cost :
    (gasSteps_copy0 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 69 := by
  unfold gasSteps_copy0
  simp

def gasSteps_copy1 :
    GasSteps (stW s 2533 ([Bm1,0,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2555 ([Bm1,0,byte,offset,outerW,(value 1 Bm1 byte acc m),base,m] ++ rest)) := by
  refine (body1 s rest Bm1 byte offset outerW acc base m hs hrest 0).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 6 - UInt256.ofNat 0 = UInt256.ofNat 6 from by decide]

@[simp] theorem gasSteps_copy1_cost :
    (gasSteps_copy1 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 68 := by
  unfold gasSteps_copy1
  simp

def gasSteps_copy2 :
    GasSteps (stW s 2555 ([Bm1,0,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2577 ([Bm1,0,byte,offset,outerW,(value 2 Bm1 byte acc m),base,m] ++ rest)) := by
  refine (body2 s rest Bm1 byte offset outerW acc base m hs hrest 0).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 5 - UInt256.ofNat 0 = UInt256.ofNat 5 from by decide]

@[simp] theorem gasSteps_copy2_cost :
    (gasSteps_copy2 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 68 := by
  unfold gasSteps_copy2
  simp

def gasSteps_copy3 :
    GasSteps (stW s 2577 ([Bm1,0,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2510 ([Bm1,4,byte,offset,outerW,(value 3 Bm1 byte acc m),base,m] ++ rest)) := by
  refine ((body3 s rest Bm1 byte offset outerW acc base m hs hrest 0).trans (control s rest Bm1 byte offset outerW (stepValue 4 0 Bm1 byte acc m) base m hs hrest 0 (by decide))).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 4 - UInt256.ofNat 0 = UInt256.ofNat 4 from by decide]

@[simp] theorem gasSteps_copy3_cost :
    (gasSteps_copy3 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 102 := by
  unfold gasSteps_copy3
  simp

def gasSteps_copy4 :
    GasSteps (stW s 2510 ([Bm1,4,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2533 ([Bm1,4,byte,offset,outerW,(value 4 Bm1 byte acc m),base,m] ++ rest)) := by
  refine ((start s rest Bm1 byte offset outerW acc base m hs hrest 4).trans (body0 s rest Bm1 byte offset outerW acc base m hs hrest 4)).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 7 - UInt256.ofNat 4 = UInt256.ofNat 3 from by decide]

@[simp] theorem gasSteps_copy4_cost :
    (gasSteps_copy4 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 69 := by
  unfold gasSteps_copy4
  simp

def gasSteps_copy5 :
    GasSteps (stW s 2533 ([Bm1,4,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2555 ([Bm1,4,byte,offset,outerW,(value 5 Bm1 byte acc m),base,m] ++ rest)) := by
  refine (body1 s rest Bm1 byte offset outerW acc base m hs hrest 4).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 6 - UInt256.ofNat 4 = UInt256.ofNat 2 from by decide]

@[simp] theorem gasSteps_copy5_cost :
    (gasSteps_copy5 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 68 := by
  unfold gasSteps_copy5
  simp

def gasSteps_copy6 :
    GasSteps (stW s 2555 ([Bm1,4,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2577 ([Bm1,4,byte,offset,outerW,(value 6 Bm1 byte acc m),base,m] ++ rest)) := by
  refine (body2 s rest Bm1 byte offset outerW acc base m hs hrest 4).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 5 - UInt256.ofNat 4 = UInt256.ofNat 1 from by decide]

@[simp] theorem gasSteps_copy6_cost :
    (gasSteps_copy6 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 68 := by
  unfold gasSteps_copy6
  simp

def gasSteps_copy7 :
    GasSteps (stW s 2577 ([Bm1,4,byte,offset,outerW,acc,base,m] ++ rest))
      (stW s 2616 ([Bm1,0,byte,offset,outerW,(value 7 Bm1 byte acc m),base,m] ++ rest)) := by
  refine (((body3 s rest Bm1 byte offset outerW acc base m hs hrest 4).trans (control s rest Bm1 byte offset outerW (stepValue 4 4 Bm1 byte acc m) base m hs hrest 4 (by decide))).trans (reset s rest Bm1 byte offset outerW (stepValue 4 4 Bm1 byte acc m) base m hs hrest)).cast rfl ?_
  simp [stW, value, stepValue, Challenge.EvmProof.Word.literal_eq_ofNat, show UInt256.ofNat 4 - UInt256.ofNat 4 = UInt256.ofNat 0 from by decide]

@[simp] theorem gasSteps_copy7_cost :
    (gasSteps_copy7 s rest Bm1 byte offset outerW acc base m hs hrest).cost = 112 := by
  unfold gasSteps_copy7
  simp

end Challenge.Modexp.Submission.Proofs.Bytecode.WordBitsFourCopies

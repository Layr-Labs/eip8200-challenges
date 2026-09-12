import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75Math
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75
open EvmSemantics PairedLaneUInt256Bridge Paired144Core Paired144WordRound
open Paired144WordRotation StaggerTerminal75Math
open Paired80Algorithm (leftFold rightFold)

/-- The physical exception changes only the C output of round75. -/
def step (i : Nat) (message : UInt256) (q : WordLane) : WordLane :=
  if i=75 then {StaggerAlgorithm.step i message q with d:=wordShift q.c 28}
  else StaggerAlgorithm.step i message q

def fold (message : Nat → UInt256) : Nat → WordLane → WordLane
  | 0,q => q
  | i+1,q => step i (message i) (fold message i q)

theorem fold_prefix (message : Nat → UInt256) (n : Nat) (hn : n≤75) (q : WordLane) :
    fold message n q = StaggerAlgorithm.fold message n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fold,ih (by omega)]
    simp only [step,show n≠75 from by omega,if_false,StaggerAlgorithm.fold]

theorem step76_d (l r : CryptoLane) (d : UInt256) (wl wr : UInt32)
    (hd : (bits d).getLsbD 121 = false)
    (he : UInt256.land d pairWord = (packCrypto l r).d) :
    StaggerAlgorithm.step 76 (word (pack wl.toBitVec wr.toBitVec))
      {packCrypto l r with d:=d} =
      {StaggerAlgorithm.step 76 (word (pack wl.toBitVec wr.toBitVec))
        (packCrypto l r) with e:=d} := by
  have ht := t_d_eq l r d wl.toBitVec wr.toBitVec
    Crypto.Ripemd160.K[4]!.toBitVec Crypto.Ripemd160.KP[4]!.toBitVec hd he
  change (⟨(packCrypto l r).e, _, (packCrypto l r).b,
      UInt256.land (wordShift (packCrypto l r).c 28) pairWord,d⟩ : WordLane) = _
  exact congrArg (fun t : UInt256 => (⟨(packCrypto l r).e,t,(packCrypto l r).b,
    UInt256.land (wordShift (packCrypto l r).c 28) pairWord,d⟩ : WordLane)) ht

theorem final_shape (message : Nat → UInt256) (words : Nat → UInt32)
    (l r : CryptoLane) (hm : StaggerAlgorithm.MessageReady message words 77) :
    ∃ d : UInt256,
      fold message 77 (packCrypto l (rightFold words 3 r)) =
        {packCrypto (leftFold words 77 l) (rightFold words 80 r) with e:=d} ∧
      UInt256.land d pairWord =
        (packCrypto (leftFold words 77 l) (rightFold words 80 r)).e := by
  let q75 := packCrypto (leftFold words 75 l) (rightFold words 78 r)
  let q76 := packCrypto (leftFold words 76 l) (rightFold words 79 r)
  let q77 := packCrypto (leftFold words 77 l) (rightFold words 80 r)
  let d := wordShift q75.c 28
  have h75 : StaggerAlgorithm.step 75 (message 75) q75 = q76 :=
    StaggerAlgorithm.step_of_crypto words 75 (by decide) (message 75) _ _ (hm 75 (by decide))
  have h76 : StaggerAlgorithm.step 76 (message 76) q76 = q77 :=
    StaggerAlgorithm.step_of_crypto words 76 (by decide) (message 76) _ _ (hm 76 (by decide))
  have hd : (bits d).getLsbD 121 = false := by
    change (bits (wordShift (word (pack _ _)) 28)).getLsbD 121 = false
    exact c_gap _ _
  have he : UInt256.land d pairWord = q76.d := by
    have hh := congrArg (fun q : WordLane => q.d) h75
    exact hh
  have hlast : StaggerAlgorithm.step 76 (message 76) {q76 with d:=d} = {q77 with e:=d} := by
    have hh := step76_d (leftFold words 76 l) (rightFold words 79 r) d
      (words Crypto.Ripemd160.r[76]!) (words Crypto.Ripemd160.rP[79]!) hd he
    have hm76 : message 76 = word (pack (words Crypto.Ripemd160.r[76]!).toBitVec
      (words Crypto.Ripemd160.rP[79]!).toBitVec) := by
      apply bits_injective
      rw [bits_word]
      exact hm 76 (by decide)
    rw [hm76] at h76 ⊢
    exact hh.trans (congrArg (fun q : WordLane => {q with e:=d}) h76)
  refine ⟨d, ?_, ?_⟩
  · rw [fold,step,if_neg (by decide : ¬76=75),fold,step,if_pos rfl,
      fold_prefix message 75 (by decide),
      StaggerAlgorithm.fold_crypto message words 75 (by decide) l r
        (fun i hi => hm i (by omega))]
    change StaggerAlgorithm.step 76 (message 76)
      {StaggerAlgorithm.step 75 (message 75) q75 with d:=d} = _
    rw [h75]
    exact hlast
  · exact he.trans (congrArg (fun q : WordLane => q.e) h76)

#print axioms fold_prefix
#print axioms step76_d
#print axioms final_shape
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75

import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionBranchRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFrame
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionRecurrence RecognitionAccumulator RecognitionBodyRaw RecognitionControlRaw

def stop (n k : Nat) : Nat := min (32*(n/32)) (224 + 256*(k/8))
def fullFrame (input : ByteArray) (n k : Nat) : RecognitionBodyRaw.Frame :=
  ⟨fullAcc input k, UInt256.ofNat (32*k), baseWord k,
    UInt256.ofNat (stop n k), UInt256.ofNat (32*(n/32))⟩
def clamp (f : RecognitionBodyRaw.Frame) : RecognitionBodyRaw.Frame :=
  if f.stop.toNat < f.full.toNat then f else {f with stop := f.full}

private theorem add_nat (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a+b) :=
  Word.ofNat_add_mod a b

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply PairedLaneUInt256Bridge.bits_injective
  simp only [PairedLaneUInt256Bridge.bits_xor, BitVec.xor_comm]

private theorem stop_next (n k : Nat) (hk : k < 31) (hb : boundary k = false) :
    stop n (k+1) = stop n k := by
  simp only [boundary, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hb
  have hdiv : (k+1)/8 = k/8 := by omega
  simp only [stop, hdiv]

theorem init_clamped (input : ByteArray) (n : Nat) (hn : Allowed n) :
    clamp (initResult n) = fullFrame input n 0 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [fullFrame, fullAcc]
  all_goals rfl

theorem normal_next (s : State) (n k : Nat) (hk : k < 31) (hb : boundary k = false) :
    normalResult s (fullFrame s.executionEnv.calldata n k) =
      fullFrame s.executionEnv.calldata n (k+1) := by
  have hsmall : 32*k < 2^256 := by omega
  have ha : 32+32*k = 32*(k+1) := by omega
  simp only [normalResult, fullFrame, fullAcc, compareWord, hb, Bool.false_eq_true,
    ↓reduceIte, baseWord, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall, add_nat, ha,
    stop_next n k hk hb, xor_comm]

theorem boundary_next (s : State) (n k : Nat) (hn : Allowed n) (hk : k < n/32)
    (hb : boundary k = true) :
    clamp (boundaryResult s (fullFrame s.executionEnv.calldata n k)) =
      fullFrame s.executionEnv.calldata n (k+1) := by
  have hks : k = 7 ∨ k = 15 ∨ k = 23 := by simpa [boundary, or_assoc] using hb
  rcases hks with rfl | rfl | rfl
  all_goals rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals simp only [clamp, boundaryResult, fullFrame, stop, fullAcc, compareWord, baseWord,
    boundary, Word.word_toNat_ofNat, add_nat]
  all_goals norm_num only
  all_goals simp only [xor_comm]
  all_goals rfl

theorem partial_acc (s : State) (n : Nat) (hn : Allowed n) (hsize : s.executionEnv.calldata.size = n)
    (hmod : n % 32 ≠ 0) :
    (partialResult s (fullFrame s.executionEnv.calldata n (n/32))).acc =
      resultAcc s.executionEnv.calldata n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals simp only [partialResult, fullFrame, resultAcc, hsize]
  all_goals norm_num only
  all_goals simp only [xor_comm]
  all_goals rfl

#print axioms boundary_next
#print axioms partial_acc
#print axioms init_clamped
#print axioms normal_next
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionFrame

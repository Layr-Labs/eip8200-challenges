import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80WideCoreBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Algorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80FinalWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanFactoring
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneBooleanSynthesis
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreCommon
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge Paired80WordRound Paired80WordRotate Paired80WordBoolean
inductive Reg where
  | a | b | c | d | e | factor | pair | upper | lower | k
  deriving DecidableEq

def word (r : Reg) (q : WordLane) (k : UInt256) : UInt256 := match r with
  | .a => q.a | .b => q.b | .c => q.c | .d => q.d | .e => q.e
  | .factor => Table80WideCoreBridge.wideFactorWord | .pair => pairWord | .upper => upperWord | .lower => lowerWord | .k => k

def stack (shape : List Reg) (q : WordLane) (k : UInt256) (rho : List UInt256) : List UInt256 :=
  shape.map (fun r => word r q k) ++ (Table80Raw.cache ++ rho)

theorem boolean_zero (b c d : UInt256) :
    booleanPair 0 b c d = PairedLaneBooleanFactoring.factoredWord b c d upperWord :=
  PairedLaneBooleanFactoring.factored_word b c d upperWord

theorem boolean_four (b c d : UInt256) :
    booleanPair 4 b c d = PairedLaneBooleanFactoring.factoredWord b c d lowerWord :=
  PairedLaneBooleanFactoring.factored_word b c d lowerWord

theorem boolean_one (b c d : UInt256) :
    booleanPair 1 b c d = PairedLaneBooleanSynthesis.oneWord b c d upperWord :=
  PairedLaneBooleanSynthesis.word_one b c d upperWord

theorem boolean_three (b c d : UInt256) :
    booleanPair 3 b c d = PairedLaneBooleanSynthesis.threeWord b c d upperWord :=
  PairedLaneBooleanSynthesis.word_three b c d upperWord
theorem add_comm (a b : UInt256) : UInt256.add a b = UInt256.add b a := by
  apply bits_injective
  simp only [bits_add]
  exact BitVec.add_comm _ _
theorem add_assoc (a b c : UInt256) : UInt256.add (UInt256.add a b) c = UInt256.add a (UInt256.add b c) := by
  apply bits_injective
  simp only [bits_add]
  exact BitVec.add_assoc _ _ _
theorem add_left_comm (a b c : UInt256) : UInt256.add a (UInt256.add b c) = UInt256.add b (UInt256.add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]
theorem mul_comm (a b : UInt256) : UInt256.mul a b = UInt256.mul b a := by
  apply bits_injective
  simp only [bits_mul]
  exact BitVec.mul_comm _ _
theorem mul_one (a : UInt256) : UInt256.mul (UInt256.ofNat 1) a = a := by
  apply bits_injective
  simp only [bits_mul, bits_ofNat]
  exact BitVec.one_mul _
theorem land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a :=
  Word.land_comm a b
theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a :=
  Word.lor_comm a b
theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply bits_injective
  rw [bits_xor, bits_xor]
  exact BitVec.xor_comm _ _
theorem xor_assoc (a b c : UInt256) : UInt256.xor (UInt256.xor a b) c = UInt256.xor a (UInt256.xor b c) := by
  apply bits_injective
  simp only [bits_xor]
  exact BitVec.xor_assoc _ _ _
theorem xor_left_comm (a b c : UInt256) : UInt256.xor a (UInt256.xor b c) = UInt256.xor b (UInt256.xor a c) := by
  rw [← xor_assoc, xor_comm a b, xor_assoc]
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreCommon

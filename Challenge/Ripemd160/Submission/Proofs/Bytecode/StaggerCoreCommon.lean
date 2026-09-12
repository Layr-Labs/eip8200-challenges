import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerAlgorithm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation
inductive Reg where
  | a | b | c | d | e | ar | br | cr | dr | er | factor | pair | upper | lower | k
  | literal (value : Nat)
  | cachedMessage (address : Nat)
  | cache (address : Nat)
  deriving DecidableEq

def word (memory : ByteArray) (h4 : UInt256) (r : Reg) (q right : WordLane) (k : UInt256) : UInt256 := match r with
  | .a => q.a | .b => q.b | .c => q.c | .d => q.d | .e => q.e
  | .ar => right.a | .br => right.b | .cr => right.c | .dr => right.d | .er => right.e
  | .factor => factorWord | .pair => pairWord | .upper => upperWord | .lower => lowerWord | .k => k
  | .literal value => UInt256.ofNat value
  | .cachedMessage address => MachineState.readWord memory address
  | .cache address => match address with
    | 140 => compactMaskWord
    | 190 => coefficientWord 0 2
    | 310 => coefficientWord 0 3
    | 350 => coefficientWord 3 0
    | 500 => h4
    | _ => MachineState.readWord memory (address / 10 * 18)

def stack (memory : ByteArray) (h4 : UInt256) (shape : List Reg) (q right : WordLane) (k : UInt256)
    (rho : List UInt256) : List UInt256 :=
  shape.map (fun r => word memory h4 r q right k) ++ rho

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
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon

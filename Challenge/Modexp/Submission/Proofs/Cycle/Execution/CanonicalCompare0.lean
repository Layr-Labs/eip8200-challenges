import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Execution
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast

def canonicalCompare0part0Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .LT,
   .push 3 10409]

def canonicalCompare0part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt x13 x8
  {s with pc := UInt256.ofNat 10241, memory := s.memory, stack := (UInt256.ofNat 10409) :: v0 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem canonicalCompare0part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions canonicalCompare0part0Program {s with pc := UInt256.ofNat 10234, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (canonicalCompare0part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  simp [hz, hzn, canonicalCompare0part0Program, canonicalCompare0part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc]


def canonicalCompare0Program : List Instr :=
  [.op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨14, by decide⟩),
   .op .LT,
   .push 3 10409]

def canonicalCompare0Model (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := UInt256.lt a8 n8
  {s with pc := UInt256.ofNat 10241, memory := s.memory, stack := (UInt256.ofNat 10409) :: v0 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest}

theorem canonicalCompare0_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions canonicalCompare0Program {s with pc := UInt256.ofNat 10234, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (canonicalCompare0Model s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := UInt256.lt a8 n8
  have h0 : runInstructions canonicalCompare0part0Program {s with pc := UInt256.ofNat 10234, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10241, memory := s.memory, stack := (UInt256.ofNat 10409) :: v0 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [canonicalCompare0part0Model, v0] using canonicalCompare0part0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  exact h0


end CycleSubmission.Execution

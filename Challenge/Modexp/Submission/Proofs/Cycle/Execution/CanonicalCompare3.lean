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

def canonicalCompare3part0Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op .GT,
   .push 2 10857]

def canonicalCompare3part0Model (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.gt v0 x6
  {s with pc := UInt256.ofNat 10724, memory := s.memory, stack := (UInt256.ofNat 10857) :: v1 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest}

theorem canonicalCompare3part0_run (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions canonicalCompare3part0Program {s with pc := UInt256.ofNat 10716, stack := x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: rest} =
      some (canonicalCompare3part0Model s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 rest) := by
  have hz : ({val := 0} : UInt256) = UInt256.ofNat 0 := rfl
  have hzn : ({val := 0} : UInt256).toNat = 0 := rfl
  have capacity (j : Nat) (hj : j ≤ 16) : rest.length + j < 1024 := by omega
  have ha160 : (160 : UInt256).toNat = 160 := rfl
  have hf160 := Monpro.activeWords_fix s 160 32 (by decide) (by norm_num) hact
  simp [hz, hzn, canonicalCompare3part0Program, canonicalCompare3part0Model, runInstructions, Challenge.EvmProof.Stepper.runInstr, List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, State.activeWordsAfterUInt256, Challenge.EvmProof.Word.literal_eq_ofNat, capacity, Nat.add_assoc, ha160, hf160]


def canonicalCompare3Program : List Instr :=
  [.op (.Dup ⟨6, by decide⟩),
   .push 1 160,
   .op .MLOAD,
   .op .GT,
   .push 2 10857]

def canonicalCompare3Model (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256) : State :=
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.gt v0 n7
  {s with pc := UInt256.ofNat 10724, memory := s.memory, stack := (UInt256.ofNat 10857) :: v1 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest}

theorem canonicalCompare3_run (s : State) (n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions canonicalCompare3Program {s with pc := UInt256.ofNat 10716, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} =
      some (canonicalCompare3Model s n2 n6 n4 a1 a2 n5 n7 P n8 n1 MASK n0 n3 a8 rest) := by
  let v0 : UInt256 := MachineState.readWord s.memory 160
  let v1 : UInt256 := UInt256.gt v0 n7
  have h0 : runInstructions canonicalCompare3part0Program {s with pc := UInt256.ofNat 10716, memory := s.memory, stack := n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} = some {s with pc := UInt256.ofNat 10724, memory := s.memory, stack := (UInt256.ofNat 10857) :: v1 :: n2 :: n6 :: n4 :: a1 :: a2 :: n5 :: n7 :: P :: n8 :: n1 :: MASK :: n0 :: n3 :: a8 :: rest} := by
    simpa only [canonicalCompare3part0Model, v0, v1] using canonicalCompare3part0_run (s) (n2) (n6) (n4) (a1) (a2) (n5) (n7) (P) (n8) (n1) (MASK) (n0) (n3) (a8) rest hcap hact
  exact h0


end CycleSubmission.Execution

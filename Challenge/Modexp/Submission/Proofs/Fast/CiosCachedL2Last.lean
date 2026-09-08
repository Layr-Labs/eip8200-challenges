import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true

/-! The final L2 suffix need not update pointers immediately discarded by POPs.
No equality of the intermediate pointer values is asserted. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Last

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof.Stepper Challenge.EvmProof.Word

def runProgram : List Instr → State → Option State
  | [], s => some s
  | op :: ops, s => (runInstr op s).bind (runProgram ops)

theorem run_append (a b : List Instr) (s : State) :
    runProgram (a ++ b) s = (runProgram a s).bind (runProgram b) := by
  induction a generalizing s with
  | nil => rfl
  | cons op a ih => simp [runProgram, ih, Option.bind_assoc]

def oldTail : List Instr :=
  [.push 1 32, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨12, by decide⟩), .op .ADD,
   .op (.Swap ⟨3, by decide⟩), .op .ADD, .op .MSTORE,
   .op (.Dup ⟨9, by decide⟩), .op .ADD]

def lastTail : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 6 32, .op .ADD, .op .MSTORE]

def discardPointers : List Instr := [.op .POP, .op .POP]

def input (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [sum, pm, pt, carry, mu, bi, pbi, paEnd, pbEnd, flag,
                     cache, ones, dst, ret] ++ rest }

def stored (s : State) (sum pt : UInt256) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded sum.toNat 32) (pt + UInt256.ofNat 32).toNat }

def output (s : State) (pc : Nat)
    (sum _pm pt nextPm nextPt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) : State :=
  { (stored s sum pt) with
    pc := UInt256.ofNat (pc + 10)
    stack := [nextPm, nextPt, carry, mu, bi, pbi, paEnd, pbEnd, flag,
              cache, ones, dst, ret] ++ rest }

theorem run_old (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (pt + UInt256.ofNat 32).toNat 32) = s.activeWords) :
    runProgram oldTail (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) =
      some (output s pc sum pm pt (cache + pm) (cache + pt)
        carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp [runProgram, oldTail, input, output, stored, runInstr,
    hc13, hc14, hc15, hc16, hc17, h32, List.exchange,
    State.activeWordsAfterUInt256, hactive, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc]

theorem run_last (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (pt + UInt256.ofNat 32).toNat 32) = s.activeWords) :
    runProgram lastTail (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) =
      some (output s pc sum pm pt pm pt
        carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have hplus : UInt256.ofNat 32 + pt = pt + UInt256.ofNat 32 := word_add_comm _ _
  simp [runProgram, lastTail, input, output, stored, runInstr,
    hc14, hc15, hc16, h32, hplus,
    State.activeWordsAfterUInt256, hactive, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc]

/-- Even the cached word may be arbitrary: both computed pointers are discarded. -/
theorem after_discard_eq (s : State) (pc : Nat)
    (sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      s.activeWords.toNat (pt + UInt256.ofNat 32).toNat 32) = s.activeWords) :
    runProgram (lastTail ++ discardPointers)
      (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) =
    runProgram (oldTail ++ discardPointers)
      (input s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  rw [run_append, run_append,
    run_old s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest hrest hactive,
    run_last s pc sum pm pt carry mu bi pbi paEnd pbEnd flag cache ones dst ret rest hrest hactive]
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  simp [runProgram, discardPointers, output, runInstr, hc12, hc13]

theorem existing_capacity (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    rest.length + 17 < 1024 := by omega

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL2Last

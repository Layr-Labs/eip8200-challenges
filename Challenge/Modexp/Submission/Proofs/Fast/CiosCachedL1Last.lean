import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true

/-! Last L1 pointers are dead only after the two following POPs.
The padded program is a proof intermediate; the candidate packs its five bytes
into the following PUSH. No equality of intermediate pointers is asserted. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1Last

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
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .ADD,
   .op (.Swap ⟨2, by decide⟩), .op .MSTORE, .op (.Dup ⟨8, by decide⟩), .op .ADD]

def lastTail : List Instr := [.op (.Dup ⟨2, by decide⟩), .op .MSTORE]

def paddedTail : List Instr := lastTail ++
  [.op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

def discardPointers : List Instr := [.op .POP, .op .POP]

def following (width : Fin 33) : List Instr := [.op (.Dup ⟨0, by decide⟩), .push width 8224]

def input (s : State) (pc : Nat)
    (sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [sum, pa, pt, carry, bi, pbi, paEnd, pbEnd, flag,
                     cache, ones, dst, ret] ++ rest }

def stored (s : State) (sum pt : UInt256) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded sum.toNat 32) pt.toNat
    activeWords := s.activeWordsAfterUInt256 pt.toNat 32 }

def output (s : State) (pc : Nat)
    (sum pt nextPa nextPt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) : State :=
  { (stored s sum pt) with
    pc := UInt256.ofNat (pc + 7)
    stack := [nextPa, nextPt, carry, bi, pbi, paEnd, pbEnd, flag,
              cache, ones, dst, ret] ++ rest }

theorem run_old (s : State) (pc : Nat)
    (sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runProgram oldTail (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) =
      some (output s pc sum pt (cache + pa) (cache + pt)
        carry bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [runProgram, oldTail, input, output, stored, runInstr,
    hc12, hc13, hc14, hc15, List.exchange,
    State.activeWordsAfterUInt256, succ_ofNat_mod, Nat.add_assoc]

theorem run_padded (s : State) (pc : Nat)
    (sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runProgram paddedTail (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) =
      some (output s pc sum pt pa pt
        carry bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  simp [runProgram, paddedTail, lastTail, input, output, stored, runInstr,
    hc12, hc13, hc14, State.activeWordsAfterUInt256, succ_ofNat_mod, Nat.add_assoc]

/-- The cached word and both old pointers are arbitrary; equality is after POPs. -/
theorem after_discard_eq (s : State) (pc : Nat)
    (sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runProgram (paddedTail ++ discardPointers)
      (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) =
    runProgram (oldTail ++ discardPointers)
      (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  rw [run_append, run_append,
    run_old s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest hrest,
    run_padded s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest hrest]
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  simp [runProgram, discardPointers, output, runInstr, hc11, hc12]

/-- The actual same-length span contains no padding: PUSH7 absorbs five bytes. -/
theorem packed_continuation_eq (s : State) (pc : Nat)
    (sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1006) :
    runProgram (oldTail ++ discardPointers ++ following 2)
      (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) =
    runProgram (lastTail ++ discardPointers ++ following 7)
      (input s pc sum pa pt carry bi pbi paEnd pbEnd flag cache ones dst ret rest) := by
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  simp [runProgram, oldTail, lastTail, discardPointers, following, input, runInstr,
    hc10, hc11, hc12, hc13, hc14, hc15, List.exchange,
    literal_eq_ofNat, State.activeWordsAfterUInt256, succ_ofNat_mod, ofNat_add_mod, Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedL1Last

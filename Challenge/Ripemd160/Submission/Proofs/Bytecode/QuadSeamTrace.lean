import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamTrace
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace PairRoundTemplate

def swap8 : Instr := .op (.Swap ⟨7, by decide⟩)
def oldWindow (j : Nat) : List Instr :=
  [swap8, pairSwap5, swap1, op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, swap1, pairSwap5, op .ADD]
def newWindow (j : Nat) : List Instr :=
  [swap8, swap1, op .MLOAD] ++ pairFirstBooleanOps j ++ [op .ADD, op .ADD]

/-- Full-width seam equivalence, with the shorter sequence's actual final PC.
The pointer, accumulator, every working word and ordered stack suffix are arbitrary. -/
theorem window_equivalent (j : Nat) (hj : j < 5)
    (s : State) (oldPC newPC Z p rot p' rot' ret B C A E F : UInt256)
    (rho : List UInt256) (hstack : rho.length < 1007) (hrun : s.halt = .Running) :
    runInstrSeq (newWindow j)
      {s with pc := newPC, stack := [Z,p,rot,p',rot',ret,B,C,A,E,F] ++ rho} =
    Option.map (fun out => {out with pc := pcAfter newPC (newWindow j)})
      (runInstrSeq (oldWindow j)
        {s with pc := oldPC, stack := [Z,p,rot,p',rot',ret,B,C,A,E,F] ++ rho}) := by
  have hcap (m : Nat) (hm : m ≤ 16) : rho.length + m < 1024 := by omega
  have hadd (u v : UInt256) : u.add v = u + v := rfl
  interval_cases j <;>
    simp (config := { maxSteps := 3000000 })
      [oldWindow, newWindow, swap8, pairFirstBooleanOps,
       pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5,
       swap1, op, runInstrSeq, Stepper.runInstr, pcAfter,
       List.exchange, hrun, hcap, UInt256.succ, Instr.size, Instr.size_op,
       State.activeWordsAfterUInt256, hadd, Word.word_add_comm,
       Word.ofNat_add_mod, Word.word_toNat_ofNat, Nat.add_assoc]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamTrace

import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Quad helper seam cancellation

The legacy first pair ended with `SWAP5`.  After the fixed inter-pair
`SWAP1`, the cached second pair performed another `SWAP1; SWAP5` around its
first Boolean result.  The two instruction sequences below act identically
on the complete live seam stack, including their message-word load.  The
active form uses three sequential `JUMPDEST`s in the corresponding slots.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PairRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadGapTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate

def legacySeam (j : Nat) : List Instr :=
  [pairSwap5, swap1, op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, swap1, pairSwap5, op .ADD]

def optimizedSeam (j : Nat) : List Instr :=
  [op .JUMPDEST, swap1, op .MLOAD] ++ pairFirstBooleanOps j ++
    [op .ADD, op .JUMPDEST, op .JUMPDEST, op .ADD]

/-- The byte-identical prefix before the three-instruction seam. -/
def seamPrefix (j : Nat) (constant : UInt256) : List Instr :=
  (firstFTemplate j constant).dropLast

/-- The byte-identical suffix after the three-instruction seam. -/
def seamSuffix (j : Nat) (constant : UInt256) : List Instr :=
  (cachedTailFTemplate j constant).drop
    (1 + (pairFirstBooleanOps j).length + 4)

theorem legacy_factor (j : Nat) (hj : j < 5) (constant : UInt256) :
    firstFTemplate j constant ++ [swap1] ++ cachedTailFTemplate j constant =
      seamPrefix j constant ++ legacySeam j ++ seamSuffix j constant := by
  interval_cases j <;> rfl

theorem optimized_factor (j : Nat) (hj : j < 5) (constant : UInt256) :
    optimizedFirstFTemplate j constant ++ [swap1] ++
        optimizedCachedTailFTemplate j constant =
      seamPrefix j constant ++ optimizedSeam j ++ seamSuffix j constant := by
  interval_cases j <;> rfl

private def continueRun (tail : List Instr) : Option State → Option State
  | none => none
  | some middle =>
      match tail with
      | [] => some middle
      | _ :: _ =>
          match middle.halt with
          | .Running => runInstrSeq tail middle
          | _ => none

set_option linter.unnecessarySeqFocus false in
private theorem runInstrSeq_append_nonempty
    (head : Instr) (body tail : List Instr) (s : State) :
    runInstrSeq ((head :: body) ++ tail) s =
      continueRun tail (runInstrSeq (head :: body) s) := by
  induction body generalizing head s tail with
  | nil =>
      cases hstep : Stepper.runInstr head s <;>
        cases tail <;>
        simp [runInstrSeq, continueRun, hstep] <;>
        split <;> simp_all
  | cons next rest ih =>
      cases hstep : Stepper.runInstr head s with
      | none => simp [runInstrSeq, continueRun, hstep]
      | some middle =>
          cases hhalt : middle.halt with
          | Running =>
              simpa [runInstrSeq, hstep, hhalt, continueRun] using
                ih next tail middle
          | Success => simp [runInstrSeq, continueRun, hstep, hhalt]
          | Returned => simp [runInstrSeq, continueRun, hstep, hhalt]
          | Reverted => simp [runInstrSeq, continueRun, hstep, hhalt]
          | Exception error => simp [runInstrSeq, continueRun, hstep, hhalt]

theorem runInstrSeq_append_congr
    (firstHead secondHead : Instr) (firstBody secondBody tail : List Instr)
    (s : State)
    (heq : runInstrSeq (firstHead :: firstBody) s =
      runInstrSeq (secondHead :: secondBody) s) :
    runInstrSeq ((firstHead :: firstBody) ++ tail) s =
      runInstrSeq ((secondHead :: secondBody) ++ tail) s := by
  rw [runInstrSeq_append_nonempty, runInstrSeq_append_nonempty, heq]

set_option linter.unnecessarySimpa false in
theorem runInstrSeq_prepend_running
    {first : List Instr} {s middle : State}
    (hfirst : runInstrSeq first s = some middle)
    (hmiddle : middle.halt = .Running) (tail : List Instr) :
    runInstrSeq (first ++ tail) s = runInstrSeq tail middle := by
  induction first generalizing s middle with
  | nil =>
      simp only [List.nil_append, runInstrSeq] at hfirst ⊢
      cases hfirst
      rfl
  | cons instruction rest ih =>
      cases hrun : Stepper.runInstr instruction s with
      | none => simp [runInstrSeq, hrun] at hfirst
      | some next =>
          cases rest with
          | nil =>
              have hnext : next = middle := by
                simpa [runInstrSeq, hrun] using hfirst
              subst middle
              cases tail with
              | nil => simpa [runInstrSeq, hrun]
              | cons nextInstruction tailRest =>
                  simpa [runInstrSeq, hrun, hmiddle]
          | cons nextInstruction restTail =>
              cases hhalt : next.halt with
              | Running =>
                  have hrest :
                      runInstrSeq (nextInstruction :: restTail) next =
                        some middle := by
                    simpa [runInstrSeq, hrun, hhalt] using hfirst
                  have hjoined := ih hrest hmiddle
                  simpa [runInstrSeq, hrun, hhalt] using hjoined
              | Success => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Returned => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Reverted => simp [runInstrSeq, hrun, hhalt] at hfirst
              | Exception error => simp [runInstrSeq, hrun, hhalt] at hfirst

set_option linter.unusedSimpArgs false in
theorem runInstrSeq_optimizedSeam (j : Nat) (hj : j < 5)
    (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (optimizedSeam j)
      {s with stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho} =
    runInstrSeq (legacySeam j)
      {s with stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho} := by
  have hcap (n : Nat) (hn : n ≤ 16) : rho.length + n < 1024 := by omega
  have hswap1 (u v : UInt256) (tail : List UInt256) :
      (u :: v :: tail).exchange 0 1 = some (v :: u :: tail) := by
    simpa using YulEvmCompiler.exchange_swap u v ([] : List UInt256) tail
  have hswap5 (u v w z q r : UInt256) (tail : List UInt256) :
      (u :: v :: w :: z :: q :: r :: tail).exchange 0 5 =
        some (r :: v :: w :: z :: q :: u :: tail) := by
    simpa using YulEvmCompiler.exchange_swap u r [v, w, z, q] tail
  have hadd_comm (u v : UInt256) : u + v = v + u := by
    apply Challenge.EvmProof.Word.word_ext
    change (u.val + v.val).val = (v.val + u.val).val
    rw [Fin.val_add, Fin.val_add, Nat.add_comm]
  interval_cases j <;>
    simp (config := { maxSteps := 2000000 }) (discharger := omega)
      [optimizedSeam, legacySeam, pairFirstBooleanOps,
        pairDup7, pairDup8, pairDup9, pairDup10, pairSwap5,
        op, dup1, dup2, dup3, dup4, dup5, dup6,
        swap1, swap2, swap3, swap4, runInstrSeq, Stepper.runInstr,
        hrun, hcap, Nat.add_assoc,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        State.activeWordsAfterUInt256, hadd_comm, hswap1, hswap5]

theorem runInstrSeq_optimizedSeam_context (j : Nat) (hj : j < 5)
    (tail : List Instr)
    (s : State) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hrun : s.halt = .Running) :
    runInstrSeq (optimizedSeam j ++ tail)
      {s with stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho} =
    runInstrSeq (legacySeam j ++ tail)
      {s with stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho} := by
  simpa [optimizedSeam, legacySeam, List.append_assoc] using
    runInstrSeq_append_congr
      (op .JUMPDEST) pairSwap5
      ([swap1, op .MLOAD] ++ pairFirstBooleanOps j ++
        [op .ADD, op .JUMPDEST, op .JUMPDEST, op .ADD])
      ([swap1, op .MLOAD] ++ pairFirstBooleanOps j ++
        [op .ADD, swap1, pairSwap5, op .ADD])
      tail
      {s with stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho}
      (runInstrSeq_optimizedSeam j hj s x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
        rho hstack hrun)

theorem runInstrSeq_optimized_quad_context (j : Nat) (hj : j < 5)
    (constant : UInt256) (start seamBase : State)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : UInt256)
    (rho : List UInt256) (hstack : rho.length < 1007)
    (hprefix : runInstrSeq (seamPrefix j constant) start =
      some {seamBase with
        stack := [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10] ++ rho})
    (hrun : seamBase.halt = .Running) :
    runInstrSeq
        (optimizedFirstFTemplate j constant ++ [swap1] ++
          optimizedCachedTailFTemplate j constant) start =
      runInstrSeq
        (firstFTemplate j constant ++ [swap1] ++
          cachedTailFTemplate j constant) start := by
  rw [optimized_factor j hj constant, legacy_factor j hj constant]
  rw [List.append_assoc, List.append_assoc]
  rw [runInstrSeq_prepend_running hprefix (by simpa using hrun),
    runInstrSeq_prepend_running hprefix (by simpa using hrun)]
  exact runInstrSeq_optimizedSeam_context j hj (seamSuffix j constant)
    seamBase x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 rho hstack hrun

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSeamCancel

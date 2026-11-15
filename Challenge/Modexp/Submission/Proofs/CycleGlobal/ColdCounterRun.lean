import Challenge.Modexp.Submission.Proofs.Prepared.ColdCounterSplit
import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.Fast.Shift
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
local notation "N" => UInt256.ofNat
namespace ColdCounterRun
def state (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
 {s with pc := N 10988,memory := mem,stack := Monpro.maxWord::N k::entrySlots z mem n bsize esize++outer n bsize esize msize}
def exitState (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 {s with pc := N 10993,memory := mem,stack := N 0::entrySlots z mem n bsize esize++outer n bsize esize msize}
def rest (z : UInt256) (mem : ByteArray) (n bsize esize msize : Nat) : List UInt256 :=
 (entrySlots z mem n bsize esize).tail++outer n bsize esize msize
private theorem rest_cap (z : UInt256) (mem : ByteArray) (n bsize esize msize : Nat) :
 (rest z mem n bsize esize msize).length≤1000 := by
 simp [rest,entrySlots,outer,Exp.outer]
theorem run_more (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize k : Nat)
 (hk : 2≤k) (hk32 : k≤32)
 (hj : Decode.isValidJumpDest s.executionEnv.code (headWord mem n).toNat=true) :
 runInstructions CycleSubmission.ColdCounterSplit.coldPrefix (state z s mem n bsize esize msize k) =
 some (afterCsubState z s mem n bsize esize msize k) := by
 have hdec : N k-N 1=N (k-1) := by interval_cases k <;> decide
 have hzero : (N k-N 1).toNat≠0 := by
  rw [hdec,Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  omega
 have raw := CycleSubmission.ColdCounterSplit.run_cold_more ({s with memory:=mem}) (N k)
  (headWord mem n) (rest z mem n bsize esize msize) (rest_cap _ _ _ _ _ _) hzero hj
 simpa [state,rest,afterCsubState,slotKState,CycleSubmission.ColdCounterSplit.state,entrySlots,hdec,headWord]
  using raw
theorem run_last (z : UInt256) (s : State) (mem : ByteArray) (n bsize esize msize : Nat) :
 runInstructions CycleSubmission.ColdCounterSplit.coldPrefix (state z s mem n bsize esize msize 1) =
 some (exitState z s mem n bsize esize msize) := by
 have raw := CycleSubmission.ColdCounterSplit.run_cold_last ({s with memory:=mem})
  (headWord mem n) (rest z mem n bsize esize msize) (rest_cap _ _ _ _ _ _)
 simpa [state,rest,exitState,CycleSubmission.ColdCounterSplit.state,entrySlots] using raw
end ColdCounterRun
end CycleSubmission.Global.Fast.Shift

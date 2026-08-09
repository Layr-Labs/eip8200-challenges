import Challenge.Sha256.Submission.Proofs.Bytecode.Schedule
import Challenge.Sha256.Submission.Proofs.Bytecode.LocatedRange
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.PairConditionTest

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem wordOfNatZero : UInt256.ofNat 0 = 0 := by decide

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def path : List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨479, YulEvmCompiler.Instr.op (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨480, YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨481, YulEvmCompiler.Instr.push 1 64, by rfl, by decide⟩,
   ⟨482, YulEvmCompiler.Instr.op (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨483, YulEvmCompiler.Instr.op (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨484, YulEvmCompiler.Instr.push 2 935, by rfl, by decide⟩,
   ⟨485, YulEvmCompiler.Instr.op (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI)), by rfl, wfOp (by decide) trivial rfl⟩]

def before (s : State) (msg ret : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 633
           stack := [UInt256.ofNat j, msg, ret] ++ rest }

def after (s : State) (msg ret : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 643
           stack := [UInt256.ofNat j, msg, ret] ++ rest }

def folded (s : State) (msg ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 938
           stack := [0, msg, ret] ++ rest }

@[simp] private theorem conditionPC (i : Nat) (hlo : 479 ≤ i) (hhi : i ≤ 485) :
    Artifact.referenceArtifact.instructionPC i =
      [633, 634, 635, 637, 638, 639, 642][i - 479]! := by
  interval_cases i <;> decide

@[simp] private theorem exitPC (i : Nat) (hlo : 646 ≤ i) (hhi : i ≤ 648) :
    Artifact.referenceArtifact.instructionPC i =
      [935, 936, 937][i - 646]! := by
  interval_cases i <;> decide

set_option linter.unusedSimpArgs false in
theorem run (s : State) (msg ret : UInt256) (rest : List UInt256)
    (j : Nat) (hj : j < 64) (hcap : rest.length < 1000)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock path (before s msg ret rest j) =
      some (after s msg ret rest j) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h0 : (0 : UInt256).toNat = 0 := by decide
  simp [path,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    before, after, hc3, hc4, hc5, hrun, UInt256.eq, UInt256.isTrue,
    hjWord, h64, h0, Challenge.EvmProof.Word.word_toNat_ofNat,
    show (64 : Nat) ≠ j by omega]

set_option linter.unusedSimpArgs false in
theorem runExit (s : State) (msg ret : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPath
      (before s msg ret rest 64) = some (folded s msg ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have h64 : (64 : UInt256).toNat = 64 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have h935 : (935 : UInt256).toNat = 935 := by decide
  have h936 : (936 : UInt256).toNat = 936 := by decide
  have h937 : (937 : UInt256).toNat = 937 := by decide
  have hs935 : UInt256.succ (935 : UInt256) = 936 := by decide
  have hs936 : UInt256.succ (936 : UInt256) = 937 := by decide
  have hs937 : UInt256.succ (937 : UInt256) = 938 := by decide
  have hdest935 : Decode.isValidJumpDest submissionBytecode 935 = true := by decide
  simp [exitPath, path, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    before, folded, List.exchange, hc2, hc3, hc4, hc5, hcode, hrun,
    UInt256.eq, UInt256.isTrue, h64, h1, h0, h935, h936, h937,
    hs935, hs936,
    hs937, hdest935,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  constructor <;> decide

end Challenge.Sha256.Submission.Proofs.Bytecode.PairConditionTest

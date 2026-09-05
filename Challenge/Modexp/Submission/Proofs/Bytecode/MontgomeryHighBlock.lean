import Challenge.EvmProof.Meter
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Exact EVM bridge for the Montgomery high-half block

The block at PC 1427 computes the high 256-bit word of `x*y`.  Its only
observable changes are the program counter and the four-word call frame's
stack prefix; memory, active words, and the caller suffix are preserved.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHighBlock

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Montgomery

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def highPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1052 .JUMPDEST, pushAt 1053 0 0, opAt 1054 .NOT,
   opAt 1055 (.Dup ⟨2, by decide⟩), opAt 1056 (.Dup ⟨2, by decide⟩),
   opAt 1057 .MULMOD, opAt 1058 (.Dup ⟨3, by decide⟩),
   opAt 1059 (.Dup ⟨1, by decide⟩), opAt 1060 .LT,
   opAt 1061 (.Swap ⟨0, by decide⟩), opAt 1062 (.Dup ⟨4, by decide⟩),
   opAt 1063 (.Swap ⟨0, by decide⟩), opAt 1064 .SUB,
   opAt 1065 .SUB, opAt 1066 (.Swap ⟨2, by decide⟩),
   opAt 1067 .POP, opAt 1068 .POP, opAt 1069 .POP,
   opAt 1070 (.Swap ⟨0, by decide⟩), opAt 1071 .JUMP]

def highEntry (s : State) (x y lo returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1427
           stack := [x, y, lo, returnDest] ++ rest }

def highReturned (s : State) (x y : UInt256) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest
           stack := [HighArithmetic.fullHighWord x y] ++ rest }

@[simp] private theorem highPCs (i : Nat) (hi : 1052 ≤ i) (hii : i ≤ 1071) :
    Artifact.submissionArtifact.instructionPC i =
      [1427,1428,1429,1430,1431,1432,1433,1434,1435,1436,
       1437,1438,1439,1440,1441,1442,1443,1444,1445,1446][i - 1052]! := by
  interval_cases i <;> decide

@[simp] private theorem highJumpDest :
    Decode.isValidJumpDest submissionBytecode 1427 = true :=
  Artifact.isValidJumpDest_index 1052 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_high (s : State) (x y lo returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hlo : lo = x * y)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock highPath
      (highEntry s x y lo returnDest rest) =
        some (highReturned s x y returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := by decide
  have hnot : UInt256.lnot ({ val := 0 } : UInt256) =
      HighArithmetic.maxWord := by
    apply Challenge.EvmProof.Word.word_ext
    change (2 ^ 256 - 1 - 0) % 2 ^ 256 = (2 ^ 256 - 1) % 2 ^ 256
    omega
  have hnot' : UInt256.lnot (UInt256.ofNat 0) = HighArithmetic.maxWord := by
    rw [← hzero]
    exact hnot
  have hcode' : (highEntry s x y lo returnDest rest).executionEnv.code =
      submissionBytecode := by
    simpa [highEntry] using hcode
  have hrun' : (highEntry s x y lo returnDest rest).halt = .Running := by
    simpa [highEntry] using hrun
  have hpc : (UInt256.ofNat 1427).succ = UInt256.ofNat 1428 := by
    exact Challenge.EvmProof.Word.succ_ofNat_mod 1427
  simp (config := { maxSteps := 200000 })
    [highPath, opAt, pushAt, wfOp, highEntry, highReturned, highPCs,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     Challenge.EvmProof.Word.word_toNat_sub,
     Challenge.EvmProof.Word.word_toNat_lt,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt,
     State.fork, State.activeWordsAfterUInt256, hcap, hc1, hc2, hc3, hc4,
     hc5, hc6, hc7, hzero, hzeroNat, hnot, hnot', hlo, hcode', hrun', hpc,
     hcode, hrun, highJumpDest, hvalid, HighArithmetic.fullHighWord,
     List.exchange]

def gasSteps_high (s : State) (x y lo returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hlo : lo = x * y)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (highEntry s x y lo returnDest rest)
      (highReturned s x y returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka highPath
      (by simpa [highEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [highEntry, State.fork] using hfork)
      (run_high s x y lo returnDest rest hcap hlo hcode hvalid hrun)
      (by simpa [highEntry] using hrun)
      (by simpa [highEntry, State.fork] using hnp)

theorem gasSteps_high_cost (s : State) (x y lo returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (hlo : lo = x * y)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (gasSteps_high s x y lo returnDest rest hcap hlo hcode hfork hvalid hrun hnp).cost =
      64 := by
  have hstatic : Challenge.EvmProof.Meter.runLocatedBlockStaticCost highPath = 64 := by
    decide
  have hpotential :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      highPath 64
      (run_high s x y lo returnDest rest hcap hlo hcode hvalid hrun)
      (by simpa [highEntry, State.fork] using hfork)
      (by decide) hstatic
  have hzeroMem :
      MachineState.memCost (highEntry s x y lo returnDest rest).activeWords.toNat =
        MachineState.memCost (highReturned s x y returnDest rest).activeWords.toNat := by
    rfl
  change Challenge.EvmProof.Stepper.runLocatedBlockCost highPath
      (highEntry s x y lo returnDest rest) = 64
  have hgasCost :
      Challenge.EvmProof.Stepper.runLocatedBlockCost highPath
          (highEntry s x y lo returnDest rest) +
        MachineState.memCost (highEntry s x y lo returnDest rest).activeWords.toNat =
      64 + MachineState.memCost (highReturned s x y returnDest rest).activeWords.toNat :=
    hpotential
  rw [hzeroMem] at hgasCost
  omega

theorem highReturned_toNat (s : State) (x y returnDest : UInt256)
    (rest : List UInt256) :
    (highReturned s x y returnDest rest).stack.head? =
      some (HighArithmetic.fullHighWord x y) := by
  rfl

theorem high_result_toNat (x y : UInt256) :
    (HighArithmetic.fullHighWord x y).toNat =
      (x.toNat * y.toNat) / HighArithmetic.B :=
  HighArithmetic.fullHighWord_toNat x y

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHighBlock

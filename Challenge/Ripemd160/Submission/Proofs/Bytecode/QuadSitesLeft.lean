import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InlineQuadTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

-- Exact decode of the measured append-only candidate; public PR342 mechanism.
def leftInlineIndex : Nat → Nat
  | 0 => 2921
  | 1 => 3038
  | 2 => 3155
  | 3 => 3272
  | 4 => 3389
  | 5 => 3522
  | 6 => 3655
  | 7 => 3788
  | 8 => 3921
  | 9 => 4050
  | 10 => 4179
  | 11 => 4308
  | 12 => 4437
  | 13 => 4570
  | 14 => 4703
  | 15 => 4836
  | 16 => 4969
  | 17 => 5098
  | 18 => 5227
  | 19 => 5356
  | _ => 5485

def leftInlinePCNat : Nat → Nat
  | 0 => 5301
  | 1 => 5468
  | 2 => 5635
  | 3 => 5802
  | 4 => 5969
  | 5 => 6168
  | 6 => 6367
  | 7 => 6566
  | 8 => 6765
  | 9 => 6960
  | 10 => 7155
  | 11 => 7350
  | 12 => 7545
  | 13 => 7744
  | 14 => 7943
  | 15 => 8142
  | 16 => 8341
  | 17 => 8536
  | 18 => 8731
  | 19 => 8926
  | _ => 9121

def leftGhostPCNat : Nat → Nat
  | 0 => 5323
  | 1 => 5490
  | 2 => 5657
  | 3 => 5824
  | 4 => 5991
  | 5 => 6190
  | 6 => 6389
  | 7 => 6588
  | 8 => 6787
  | 9 => 6982
  | 10 => 7177
  | 11 => 7372
  | 12 => 7567
  | 13 => 7766
  | 14 => 7965
  | 15 => 8164
  | 16 => 8363
  | 17 => 8558
  | 18 => 8753
  | 19 => 8948
  | _ => 8948

def leftInlinePC (k : Nat) : UInt256 := UInt256.ofNat (leftInlinePCNat k)

def leftInlineTemplate (k : Fin 20) : List Instr :=
  InlineQuadTrace.template (k.val / 4) (leftConstant k) (leftReturnPC k.val)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftRotation0 k) (leftRotation1 k) (leftRotation2 k) (leftRotation3 k)

def leftInlineSite (k : Fin 20) :
    GenericRoundSite Artifact .Osaka (leftInlineTemplate k) :=
  StackSiteBuilder.ofSlice (leftInlineTemplate k) (leftInlineIndex k.val)
    (by fin_cases k <;> rfl)
    (by fin_cases k <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases k <;> decide))
    (by fin_cases k <;> decide)

theorem leftInlineSite_start (k : Fin 20) :
    (leftInlineSite k).startPC = leftInlinePC k.val := by
  fin_cases k <;> rfl

theorem leftInlineSite_end (k : Fin 20) :
    (leftInlineSite k).endPC = leftInlinePC (k.val + 1) := by
  fin_cases k <;> rfl

theorem leftghost_pc (k : Fin 20) :
    (UInt256.ofNat (leftGhostPCNat k.val)).succ =
      pcAfter (leftInlineSite k).startPC
        (InlineQuadTrace.args (leftReturnPC k.val)
          (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
          (leftRotation0 k) (leftRotation1 k) (leftRotation2 k) (leftRotation3 k)) := by
  fin_cases k <;> rfl

def leftenterPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨931, .push 2 5300, by rfl, by decide⟩,
   ⟨932, .op .JUMP, by rfl, by decide⟩,
   ⟨2920, .op .JUMPDEST, by rfl, by decide⟩]

def left_enter (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1337}
      {s with pc := UInt256.ofNat 5301} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 5300 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 2920 (by rfl)
  have hp931 : Artifact.instructionPC 931 = 1337 := by rfl
  have hp932 : Artifact.instructionPC 932 = 1340 := by rfl
  have hp2920 : Artifact.instructionPC 2920 = 5300 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka leftenterPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      leftenterPath, hp931, hp932, hp2920, hrun, hstack, hv]
  · exact hrun
  · exact hnp

def leftexitPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨5485, .push 2 1896, by rfl, by decide⟩,
   ⟨5486, .op .JUMP, by rfl, by decide⟩,
   ⟨1171, .op .JUMPDEST, by rfl, by decide⟩]

def left_exit (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 9121}
      {s with pc := UInt256.ofNat 1897} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 1896 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 1171 (by rfl)
  have hp5485 : Artifact.instructionPC 5485 = 9121 := by rfl
  have hp5486 : Artifact.instructionPC 5486 = 9124 := by rfl
  have hp1171 : Artifact.instructionPC 1171 = 1896 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka leftexitPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      leftexitPath, hp5485, hp5486, hp1171, hrun, hstack, hv]
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

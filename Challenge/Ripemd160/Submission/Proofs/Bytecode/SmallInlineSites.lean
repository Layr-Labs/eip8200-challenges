import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesLeft
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InlineQuadTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

def leftInlineIndex : Nat → Nat
  | 18 => 2919
  | 19 => 3048
  | _ => 0

def leftInlinePCNat : Nat → Nat
  | 18 => 5301
  | 19 => 5496
  | 20 => 5691
  | _ => 0

def leftGhostPCNat : Nat → Nat
  | 18 => 5323
  | 19 => 5518
  | _ => 0

def leftInlinePC (k : Nat) : UInt256 := UInt256.ofNat (leftInlinePCNat k)

def leftInlineTemplate (k : Fin 20) : List Instr :=
  InlineQuadTrace.template (k.val / 4) (leftConstant k) (leftReturnPC k.val)
    (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
    (leftRotation0 k) (leftRotation1 k) (leftRotation2 k) (leftRotation3 k)

def leftInlineSite (k : Fin 20) (hk : 18 ≤ k.val) :
    GenericRoundSite Artifact .Osaka (leftInlineTemplate k) :=
  StackSiteBuilder.ofSlice (leftInlineTemplate k) (leftInlineIndex k.val)
    (by fin_cases k <;> first | omega | rfl)
    (by fin_cases k <;> first | omega | decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases k <;> first | omega | decide))
    (by fin_cases k <;> first | omega | decide)

theorem leftInlineSite_start (k : Fin 20) (hk : 18 ≤ k.val) :
    (leftInlineSite k hk).startPC = leftInlinePC k.val := by
  fin_cases k <;> first | omega | rfl

theorem leftInlineSite_end (k : Fin 20) (hk : 18 ≤ k.val) :
    (leftInlineSite k hk).endPC = leftInlinePC (k.val + 1) := by
  fin_cases k <;> first | omega | rfl

theorem leftghost_pc (k : Fin 20) (hk : 18 ≤ k.val) :
    (UInt256.ofNat (leftGhostPCNat k.val)).succ =
      pcAfter (leftInlineSite k hk).startPC
        (InlineQuadTrace.args (leftReturnPC k.val)
          (leftAddress0 k) (leftAddress1 k) (leftAddress2 k) (leftAddress3 k)
          (leftRotation0 k) (leftRotation1 k) (leftRotation2 k) (leftRotation3 k)) := by
  fin_cases k <;> first | omega | rfl

def leftenterPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨1147, .push 3 5300, by rfl, by decide⟩,
   ⟨1148, .op .JUMP, by rfl, by decide⟩,
   ⟨2918, .op .JUMPDEST, by rfl, by decide⟩]

def left_enter (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1841}
      {s with pc := UInt256.ofNat 5301} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 5300 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 2918 (by rfl)
  have hp1147 : Artifact.instructionPC 1147 = 1841 := by rfl
  have hp1148 : Artifact.instructionPC 1148 = 1845 := by rfl
  have hp2918 : Artifact.instructionPC 2918 = 5300 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka leftenterPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      leftenterPath, hp1147, hp1148, hp2918, hrun, hstack, hv]
  · exact hrun
  · exact hnp

def leftexitPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨3177, .push 2 1896, by rfl, by decide⟩,
   ⟨3178, .op .JUMP, by rfl, by decide⟩,
   ⟨1170, .op .JUMPDEST, by rfl, by decide⟩]

def left_exit (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 5691}
      {s with pc := UInt256.ofNat 1897} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 1896 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 1170 (by rfl)
  have hp3177 : Artifact.instructionPC 3177 = 5691 := by rfl
  have hp3178 : Artifact.instructionPC 3178 = 5694 := by rfl
  have hp1170 : Artifact.instructionPC 1170 = 1896 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka leftexitPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      leftexitPath, hp3177, hp3178, hp1170, hrun, hstack, hv]
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

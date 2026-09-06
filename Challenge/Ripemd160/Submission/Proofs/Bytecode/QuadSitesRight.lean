import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.InlineQuadTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate

-- Exact decode of the measured append-only candidate; public PR342 mechanism.
def rightInlineIndex : Nat → Nat
  | 0 => 5488
  | 1 => 5617
  | 2 => 5746
  | 3 => 5875
  | 4 => 6004
  | 5 => 6137
  | 6 => 6270
  | 7 => 6403
  | 8 => 6536
  | 9 => 6665
  | 10 => 6794
  | 11 => 6923
  | 12 => 7052
  | 13 => 7185
  | 14 => 7318
  | 15 => 7451
  | 16 => 7584
  | 17 => 7701
  | 18 => 7818
  | 19 => 7935
  | _ => 8052

def rightInlinePCNat : Nat → Nat
  | 0 => 9126
  | 1 => 9321
  | 2 => 9516
  | 3 => 9711
  | 4 => 9906
  | 5 => 10105
  | 6 => 10304
  | 7 => 10503
  | 8 => 10702
  | 9 => 10897
  | 10 => 11092
  | 11 => 11287
  | 12 => 11482
  | 13 => 11681
  | 14 => 11880
  | 15 => 12079
  | 16 => 12278
  | 17 => 12445
  | 18 => 12612
  | 19 => 12779
  | _ => 12946

def rightGhostPCNat : Nat → Nat
  | 0 => 9148
  | 1 => 9343
  | 2 => 9538
  | 3 => 9733
  | 4 => 9928
  | 5 => 10127
  | 6 => 10326
  | 7 => 10525
  | 8 => 10724
  | 9 => 10919
  | 10 => 11114
  | 11 => 11309
  | 12 => 11504
  | 13 => 11703
  | 14 => 11902
  | 15 => 12101
  | 16 => 12300
  | 17 => 12467
  | 18 => 12634
  | 19 => 12801
  | _ => 12801

def rightInlinePC (k : Nat) : UInt256 := UInt256.ofNat (rightInlinePCNat k)

def rightInlineTemplate (k : Fin 20) : List Instr :=
  InlineQuadTrace.template (4 - k.val / 4) (rightConstant k) (rightReturnPC k.val)
    (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
    (rightRotation0 k) (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)

def rightInlineSite (k : Fin 20) :
    GenericRoundSite Artifact .Osaka (rightInlineTemplate k) :=
  StackSiteBuilder.ofSlice (rightInlineTemplate k) (rightInlineIndex k.val)
    (by fin_cases k <;> rfl)
    (by fin_cases k <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases k <;> decide))
    (by fin_cases k <;> decide)

theorem rightInlineSite_start (k : Fin 20) :
    (rightInlineSite k).startPC = rightInlinePC k.val := by
  fin_cases k <;> rfl

theorem rightInlineSite_end (k : Fin 20) :
    (rightInlineSite k).endPC = rightInlinePC (k.val + 1) := by
  fin_cases k <;> rfl

theorem rightghost_pc (k : Fin 20) :
    (UInt256.ofNat (rightGhostPCNat k.val)).succ =
      pcAfter (rightInlineSite k).startPC
        (InlineQuadTrace.args (rightReturnPC k.val)
          (rightAddress0 k) (rightAddress1 k) (rightAddress2 k) (rightAddress3 k)
          (rightRotation0 k) (rightRotation1 k) (rightRotation2 k) (rightRotation3 k)) := by
  fin_cases k <;> rfl

def rightenterPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨1183, .push 2 9125, by rfl, by decide⟩,
   ⟨1184, .op .JUMP, by rfl, by decide⟩,
   ⟨5487, .op .JUMPDEST, by rfl, by decide⟩]

def right_enter (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1913}
      {s with pc := UInt256.ofNat 9126} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 9125 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 5487 (by rfl)
  have hp1183 : Artifact.instructionPC 1183 = 1913 := by rfl
  have hp1184 : Artifact.instructionPC 1184 = 1916 := by rfl
  have hp5487 : Artifact.instructionPC 5487 = 9125 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka rightenterPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      rightenterPath, hp1183, hp1184, hp5487, hrun, hstack, hv]
  · exact hrun
  · exact hnp

def rightexitPath : List (Stepper.Located Artifact .Osaka) :=
  [⟨8052, .push 2 2472, by rfl, by decide⟩,
   ⟨8053, .op .JUMP, by rfl, by decide⟩,
   ⟨1423, .op .JUMPDEST, by rfl, by decide⟩]

def right_exit (s : State)
    (hstack : s.stack.length < 1023)
    (hcode : s.executionEnv.code = Artifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 12946}
      {s with pc := UInt256.ofNat 2473} := by
  have hv : Decode.isValidJumpDest s.executionEnv.code 2472 = true := by
    rw [hcode]
    exact Artifact.isValidJumpDest_index 1423 (by rfl)
  have hp8052 : Artifact.instructionPC 8052 = 12946 := by rfl
  have hp8053 : Artifact.instructionPC 8053 = 12949 := by rfl
  have hp1423 : Artifact.instructionPC 1423 = 2472 := by rfl
  apply Stepper.runLocatedBlock_sound Artifact .Osaka rightexitPath
  · exact hcode
  · exact hfork
  · simp [Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
      rightexitPath, hp8052, hp8053, hp1423, hrun, hstack, hv]
  · exact hrun
  · exact hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

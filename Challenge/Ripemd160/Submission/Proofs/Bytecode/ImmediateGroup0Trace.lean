import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0A
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0B
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0C
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# Sixteen-round left group0 trace (rounds 0..15)

First complete 16-round left group with `base=0xc0`, `j=0`, `K=0`,
`r[0..15]=0..15`, `s[0..15]` pinned. Round 0 reuses
`ImmediateWrapper.gasSteps_immediateRound`; rounds 1..15 compose each
nine-instruction body setup with the unchanged `RoundTrace.gasSteps_round`.
The recursive `groupState` threads memory across all 16 rounds with outer
stack `[messageOffset,outerReturn]++rest`. The final `GasSteps` runs from
PC `0x747` through all 16 calls to the return `JUMPDEST` after round 15
at PC `0x845` (index 1140). No functional invariant is proved here.
Static work is kernel-evaluated; predicted total is 8686 gas.
Generated deterministically; see `benchmark-results/ripemd160/h09/gen_h09_group0.py`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0Trace

open EvmSemantics
open EvmSemantics.EVM

/-- Pinned word index for group0 round `n` (`r[n]=n` for `n<16`). -/
def groupWi : Nat → UInt256
  | 0 => UInt256.ofNat 0
  | 1 => UInt256.ofNat 1
  | 2 => UInt256.ofNat 2
  | 3 => UInt256.ofNat 3
  | 4 => UInt256.ofNat 4
  | 5 => UInt256.ofNat 5
  | 6 => UInt256.ofNat 6
  | 7 => UInt256.ofNat 7
  | 8 => UInt256.ofNat 8
  | 9 => UInt256.ofNat 9
  | 10 => UInt256.ofNat 10
  | 11 => UInt256.ofNat 11
  | 12 => UInt256.ofNat 12
  | 13 => UInt256.ofNat 13
  | 14 => UInt256.ofNat 14
  | 15 => UInt256.ofNat 15
  | _ => UInt256.ofNat 0

/-- Pinned rotation for group0 round `n` (`s[0..15]`). -/
def groupRot : Nat → UInt256
  | 0 => UInt256.ofNat 11
  | 1 => UInt256.ofNat 14
  | 2 => UInt256.ofNat 15
  | 3 => UInt256.ofNat 12
  | 4 => UInt256.ofNat 5
  | 5 => UInt256.ofNat 8
  | 6 => UInt256.ofNat 7
  | 7 => UInt256.ofNat 9
  | 8 => UInt256.ofNat 11
  | 9 => UInt256.ofNat 13
  | 10 => UInt256.ofNat 14
  | 11 => UInt256.ofNat 15
  | 12 => UInt256.ofNat 6
  | 13 => UInt256.ofNat 7
  | 14 => UInt256.ofNat 9
  | 15 => UInt256.ofNat 8
  | _ => UInt256.ofNat 0

/-- Pinned return PC for group0 round `n`. -/
def groupRet : Nat → UInt256
  | 0 => UInt256.ofNat 0x755
  | 1 => UInt256.ofNat 0x765
  | 2 => UInt256.ofNat 0x775
  | 3 => UInt256.ofNat 0x785
  | 4 => UInt256.ofNat 0x795
  | 5 => UInt256.ofNat 0x7a5
  | 6 => UInt256.ofNat 0x7b5
  | 7 => UInt256.ofNat 0x7c5
  | 8 => UInt256.ofNat 0x7d5
  | 9 => UInt256.ofNat 0x7e5
  | 10 => UInt256.ofNat 0x7f5
  | 11 => UInt256.ofNat 0x805
  | 12 => UInt256.ofNat 0x815
  | 13 => UInt256.ofNat 0x825
  | 14 => UInt256.ofNat 0x835
  | 15 => UInt256.ofNat 0x845
  | _ => UInt256.ofNat 0x845

/-- Recursive memory state across the sixteen rounds. `groupState s msgOff
outerRet rest n` is the state before wrapper `n` (`n = 0` at PC `0x747` and
`n ≥ 1` at the prior return), with memory after `n` rounds. -/
def groupState (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => { s with pc := UInt256.ofNat 0x747,
             stack := [messageOffset, outerReturn] ++ rest }
  | n + 1 =>
    RoundTrace.roundReturned (groupState s messageOffset outerReturn rest n)
      (UInt256.ofNat 0xc0) 0 (groupWi n) (groupRot n) (UInt256.ofNat 0)
      (groupRet n) ([messageOffset, outerReturn] ++ rest)

/-- Final state after all 16 rounds: return `JUMPDEST` after round 15. -/
def groupFinal (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) : State :=
  groupState s messageOffset outerReturn rest 16

@[simp] private theorem valid755 :
    Decode.isValidJumpDest submissionBytecode 0x755 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1005 (by rfl)

/-- Step 0 reuses the proved first-left wrapper (PC `0x747` to `0x755`). -/
def gasSteps_step0 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 0)
      (groupState s messageOffset outerReturn rest 1) := by
  have g := ImmediateWrapper.gasSteps_immediateRound s messageOffset outerReturn rest
    hstack hcode hfork hrun hnp
  have hStart : ImmediateWrapper.wrapperEntry s messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 0 := by rfl
  have hEnd : RoundTrace.roundReturned s (UInt256.ofNat 0xc0) 0 (UInt256.ofNat 0)
      (UInt256.ofNat 11) (UInt256.ofNat 0) (UInt256.ofNat 0x755)
      ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 1 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 1: body wrapper at prior return to return `0x765`. -/
def gasSteps_step1 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 1)
      (groupState s messageOffset outerReturn rest 2) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 1).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 1).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 1).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 1).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 1).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 1).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 1).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 1).executionEnv.fork
      (groupState s messageOffset outerReturn rest 1).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 1).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0A.gasSteps_round1
    (groupState s messageOffset outerReturn rest 1) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0A.entry1
      (groupState s messageOffset outerReturn rest 1) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 1 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 1) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 1) (UInt256.ofNat 14) (UInt256.ofNat 0)
      (UInt256.ofNat 0x765) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 2 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 2: body wrapper at prior return to return `0x775`. -/
def gasSteps_step2 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 2)
      (groupState s messageOffset outerReturn rest 3) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 2).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 2).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 2).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 2).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 2).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 2).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 2).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 2).executionEnv.fork
      (groupState s messageOffset outerReturn rest 2).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 2).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0A.gasSteps_round2
    (groupState s messageOffset outerReturn rest 2) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0A.entry2
      (groupState s messageOffset outerReturn rest 2) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 2 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 2) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 2) (UInt256.ofNat 15) (UInt256.ofNat 0)
      (UInt256.ofNat 0x775) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 3 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 3: body wrapper at prior return to return `0x785`. -/
def gasSteps_step3 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 3)
      (groupState s messageOffset outerReturn rest 4) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 3).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 3).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 3).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 3).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 3).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 3).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 3).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 3).executionEnv.fork
      (groupState s messageOffset outerReturn rest 3).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 3).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0A.gasSteps_round3
    (groupState s messageOffset outerReturn rest 3) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0A.entry3
      (groupState s messageOffset outerReturn rest 3) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 3 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 3) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 3) (UInt256.ofNat 12) (UInt256.ofNat 0)
      (UInt256.ofNat 0x785) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 4 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 4: body wrapper at prior return to return `0x795`. -/
def gasSteps_step4 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 4)
      (groupState s messageOffset outerReturn rest 5) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 4).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 4).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 4).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 4).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 4).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 4).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 4).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 4).executionEnv.fork
      (groupState s messageOffset outerReturn rest 4).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 4).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0A.gasSteps_round4
    (groupState s messageOffset outerReturn rest 4) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0A.entry4
      (groupState s messageOffset outerReturn rest 4) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 4 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 4) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 4) (UInt256.ofNat 5) (UInt256.ofNat 0)
      (UInt256.ofNat 0x795) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 5 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 5: body wrapper at prior return to return `0x7a5`. -/
def gasSteps_step5 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 5)
      (groupState s messageOffset outerReturn rest 6) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 5).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 5).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 5).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 5).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 5).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 5).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 5).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 5).executionEnv.fork
      (groupState s messageOffset outerReturn rest 5).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 5).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0A.gasSteps_round5
    (groupState s messageOffset outerReturn rest 5) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0A.entry5
      (groupState s messageOffset outerReturn rest 5) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 5 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 5) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 5) (UInt256.ofNat 8) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7a5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 6 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 6: body wrapper at prior return to return `0x7b5`. -/
def gasSteps_step6 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 6)
      (groupState s messageOffset outerReturn rest 7) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 6).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 6).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 6).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 6).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 6).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 6).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 6).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 6).executionEnv.fork
      (groupState s messageOffset outerReturn rest 6).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 6).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0B.gasSteps_round6
    (groupState s messageOffset outerReturn rest 6) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0B.entry6
      (groupState s messageOffset outerReturn rest 6) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 6 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 6) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 6) (UInt256.ofNat 7) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7b5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 7 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 7: body wrapper at prior return to return `0x7c5`. -/
def gasSteps_step7 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 7)
      (groupState s messageOffset outerReturn rest 8) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 7).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 7).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 7).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 7).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 7).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 7).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 7).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 7).executionEnv.fork
      (groupState s messageOffset outerReturn rest 7).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 7).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0B.gasSteps_round7
    (groupState s messageOffset outerReturn rest 7) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0B.entry7
      (groupState s messageOffset outerReturn rest 7) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 7 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 7) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 7) (UInt256.ofNat 9) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7c5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 8 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 8: body wrapper at prior return to return `0x7d5`. -/
def gasSteps_step8 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 8)
      (groupState s messageOffset outerReturn rest 9) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 8).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 8).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 8).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 8).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 8).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 8).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 8).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 8).executionEnv.fork
      (groupState s messageOffset outerReturn rest 8).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 8).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0B.gasSteps_round8
    (groupState s messageOffset outerReturn rest 8) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0B.entry8
      (groupState s messageOffset outerReturn rest 8) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 8 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 8) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 8) (UInt256.ofNat 11) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7d5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 9 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 9: body wrapper at prior return to return `0x7e5`. -/
def gasSteps_step9 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 9)
      (groupState s messageOffset outerReturn rest 10) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 9).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 9).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 9).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 9).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 9).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 9).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 9).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 9).executionEnv.fork
      (groupState s messageOffset outerReturn rest 9).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 9).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0B.gasSteps_round9
    (groupState s messageOffset outerReturn rest 9) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0B.entry9
      (groupState s messageOffset outerReturn rest 9) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 9 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 9) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 9) (UInt256.ofNat 13) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7e5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 10 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 10: body wrapper at prior return to return `0x7f5`. -/
def gasSteps_step10 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 10)
      (groupState s messageOffset outerReturn rest 11) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 10).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 10).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 10).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 10).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 10).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 10).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 10).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 10).executionEnv.fork
      (groupState s messageOffset outerReturn rest 10).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 10).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0B.gasSteps_round10
    (groupState s messageOffset outerReturn rest 10) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0B.entry10
      (groupState s messageOffset outerReturn rest 10) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 10 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 10) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 10) (UInt256.ofNat 14) (UInt256.ofNat 0)
      (UInt256.ofNat 0x7f5) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 11 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 11: body wrapper at prior return to return `0x805`. -/
def gasSteps_step11 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 11)
      (groupState s messageOffset outerReturn rest 12) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 11).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 11).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 11).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 11).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 11).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 11).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 11).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 11).executionEnv.fork
      (groupState s messageOffset outerReturn rest 11).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 11).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0C.gasSteps_round11
    (groupState s messageOffset outerReturn rest 11) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0C.entry11
      (groupState s messageOffset outerReturn rest 11) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 11 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 11) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 11) (UInt256.ofNat 15) (UInt256.ofNat 0)
      (UInt256.ofNat 0x805) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 12 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 12: body wrapper at prior return to return `0x815`. -/
def gasSteps_step12 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 12)
      (groupState s messageOffset outerReturn rest 13) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 12).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 12).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 12).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 12).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 12).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 12).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 12).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 12).executionEnv.fork
      (groupState s messageOffset outerReturn rest 12).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 12).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0C.gasSteps_round12
    (groupState s messageOffset outerReturn rest 12) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0C.entry12
      (groupState s messageOffset outerReturn rest 12) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 12 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 12) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 12) (UInt256.ofNat 6) (UInt256.ofNat 0)
      (UInt256.ofNat 0x815) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 13 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 13: body wrapper at prior return to return `0x825`. -/
def gasSteps_step13 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 13)
      (groupState s messageOffset outerReturn rest 14) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 13).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 13).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 13).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 13).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 13).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 13).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 13).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 13).executionEnv.fork
      (groupState s messageOffset outerReturn rest 13).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 13).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0C.gasSteps_round13
    (groupState s messageOffset outerReturn rest 13) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0C.entry13
      (groupState s messageOffset outerReturn rest 13) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 13 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 13) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 13) (UInt256.ofNat 7) (UInt256.ofNat 0)
      (UInt256.ofNat 0x825) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 14 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 14: body wrapper at prior return to return `0x835`. -/
def gasSteps_step14 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 14)
      (groupState s messageOffset outerReturn rest 15) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 14).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 14).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 14).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 14).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 14).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 14).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 14).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 14).executionEnv.fork
      (groupState s messageOffset outerReturn rest 14).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 14).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0C.gasSteps_round14
    (groupState s messageOffset outerReturn rest 14) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0C.entry14
      (groupState s messageOffset outerReturn rest 14) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 14 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 14) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 14) (UInt256.ofNat 9) (UInt256.ofNat 0)
      (UInt256.ofNat 0x835) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 15 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- Step 15: body wrapper at prior return to return `0x845`. -/
def gasSteps_step15 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 15)
      (groupState s messageOffset outerReturn rest 16) := by
  have hcodeK : (groupState s messageOffset outerReturn rest 15).executionEnv.code =
      submissionBytecode := by
    have h : (groupState s messageOffset outerReturn rest 15).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    exact hcode
  have hforkK : (groupState s messageOffset outerReturn rest 15).fork = .Osaka := by
    have h : (groupState s messageOffset outerReturn rest 15).fork = s.fork := by rfl
    rw [h]
    exact hfork
  have hrunK : (groupState s messageOffset outerReturn rest 15).halt = .Running := by
    have h : (groupState s messageOffset outerReturn rest 15).halt = s.halt := by rfl
    rw [h]
    exact hrun
  have hnpK : Precompile.isPrecompileWithConfig
      (groupState s messageOffset outerReturn rest 15).executionEnv.precompileConfig
      (groupState s messageOffset outerReturn rest 15).executionEnv.fork
      (groupState s messageOffset outerReturn rest 15).executionEnv.codeAddr = false := by
    have h : (groupState s messageOffset outerReturn rest 15).executionEnv =
        s.executionEnv := by rfl
    rw [h]
    rw [h]
    exact hnp
  have g := ImmediateGroup0C.gasSteps_round15
    (groupState s messageOffset outerReturn rest 15) messageOffset outerReturn rest
    hstack hcodeK hforkK hrunK hnpK
  have hStart : ImmediateGroup0C.entry15
      (groupState s messageOffset outerReturn rest 15) messageOffset outerReturn rest =
      groupState s messageOffset outerReturn rest 15 := by rfl
  have hEnd : RoundTrace.roundReturned
      (groupState s messageOffset outerReturn rest 15) (UInt256.ofNat 0xc0) 0
      (UInt256.ofNat 15) (UInt256.ofNat 8) (UInt256.ofNat 0)
      (UInt256.ofNat 0x845) ([messageOffset, outerReturn] ++ rest) =
      groupState s messageOffset outerReturn rest 16 := by rfl
  exact Challenge.EvmProof.GasSteps.cast g hStart hEnd

/-- One `GasSteps` trace from PC `0x747` through all 16 calls to `0x845`. -/
def gasSteps_group0 (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) (hstack : rest.length < 978)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (groupState s messageOffset outerReturn rest 0)
      (groupState s messageOffset outerReturn rest 16) := by
  have g0 := gasSteps_step0 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g1 := gasSteps_step1 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g2 := gasSteps_step2 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g3 := gasSteps_step3 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g4 := gasSteps_step4 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g5 := gasSteps_step5 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g6 := gasSteps_step6 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g7 := gasSteps_step7 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g8 := gasSteps_step8 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g9 := gasSteps_step9 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g10 := gasSteps_step10 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g11 := gasSteps_step11 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g12 := gasSteps_step12 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g13 := gasSteps_step13 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g14 := gasSteps_step14 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  have g15 := gasSteps_step15 s messageOffset outerReturn rest hstack hcode hfork hrun hnp
  exact g0.trans (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans
    (g7.trans (g8.trans (g9.trans (g10.trans (g11.trans (g12.trans
      (g13.trans (g14.trans g15)))))))))))))

/-- Target PC/index after the 16th return. -/
theorem groupFinal_pc (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) :
    (groupState s messageOffset outerReturn rest 16).pc = UInt256.ofNat 0x845 := by rfl

theorem groupFinal_stack (s : State) (messageOffset outerReturn : UInt256)
    (rest : List UInt256) :
    (groupState s messageOffset outerReturn rest 16).stack =
      [messageOffset, outerReturn] ++ rest := by rfl

theorem groupFinal_valid :
    Decode.isValidJumpDest submissionBytecode 0x845 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 1140 (by rfl)

/-- Static non-memory work of the first-left wrapper (round 0, eight instructions). -/
def wrapperWork0 : Nat :=
  Challenge.EvmProof.Meter.runLocatedBlockStaticCost ImmediateWrapper.firstLeftPath

theorem wrapperWork0_eq : wrapperWork0 = 26 := by rfl

/-- Total static wrapper work for all 16 setups (round 0 plus fifteen nine-instruction bodies). -/
def groupWrapperWork : Nat :=
  wrapperWork0 + ImmediateGroup0A.wrapperWork1 + ImmediateGroup0A.wrapperWork2 + ImmediateGroup0A.wrapperWork3 + ImmediateGroup0A.wrapperWork4 + ImmediateGroup0A.wrapperWork5 + ImmediateGroup0B.wrapperWork6 + ImmediateGroup0B.wrapperWork7 + ImmediateGroup0B.wrapperWork8 + ImmediateGroup0B.wrapperWork9 + ImmediateGroup0B.wrapperWork10 + ImmediateGroup0C.wrapperWork11 + ImmediateGroup0C.wrapperWork12 + ImmediateGroup0C.wrapperWork13 + ImmediateGroup0C.wrapperWork14 + ImmediateGroup0C.wrapperWork15

theorem groupWrapperWork_eq : groupWrapperWork = 446 := by rfl

/-- Total static round-body work for `j=0` across 16 rounds. -/
def groupRoundWork : Nat :=
  16 * Challenge.EvmProof.Meter.runLocatedBlockStaticCost
    (RoundTrace.roundTracePath 0)

theorem groupRoundWork_eq : groupRoundWork = 8240 := by rfl

/-- Exact static work for the 16 wrappers plus 16 round bodies. -/
def groupStaticWork : Nat :=
  groupWrapperWork + groupRoundWork

/-- Kernel-evaluated total: `26 + 15*28 + 16*515 = 8686`. -/
theorem groupStaticWork_eq : groupStaticWork = 8686 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateGroup0Trace

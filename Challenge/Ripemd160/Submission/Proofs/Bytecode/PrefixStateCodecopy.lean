import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Generic `CODECOPY` step for the H8 checked prefix (index 4081, pc 5000).

The raw symbolic stepper has no `CODECOPY` case, so this module proves the
single step directly against `StepRunning.codecopy`, following the
`KnownInputCompactCodecopy` pattern.  It copies 32 code bytes from offset
106 to scratch word 0.  Branch proofs compose via `gasSteps_codecopy`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def preCopyState (s : State) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 5054
    stack := [UInt256.ofNat 0, UInt256.ofNat 106, UInt256.ofNat 32] ++ rho }

def copiedState (s : State) (rho : List UInt256) : State :=
  { PrefixStateMemory.copied s with
    pc := UInt256.ofNat 5055
    stack := rho }

def gasSteps_codecopy (s : State) (rho : List UInt256)
    (hstack : rho.length ≤ 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (preCopyState s rho) (copiedState s rho) := by
  let pre := preCopyState s rho
  let cost := Gas.codecopyTotal pre (UInt256.ofNat 0) (UInt256.ofNat 32)
  refine GasSteps.one cost ?_
  intro gas hgas
  have hcode' : (withGas pre gas).executionEnv.code =
      Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hpc : (withGas pre gas).pc.toNat =
      Artifact.submissionArtifact.instructionPC 4086 := by
    show (UInt256.ofNat 5048).toNat = _
    rw [PrefixStatePaths.pc4081]
    decide
  have hdec := Stepper.decodes_of_artifact
    Artifact.submissionArtifact (withGas pre gas) 4090 (.op .CODECOPY)
    hcode' hpc (by rfl) (by exact ⟨by decide, trivial, rfl⟩)
  change (withGas pre gas).decodedOp = some .CODECOPY at hdec
  apply EVM.Step.running
  · simpa [pre, preCopyState, withGas] using hrun
  · simpa [pre, preCopyState, withGas] using hnp
  · have hstack' : (withGas pre gas).stack =
        UInt256.ofNat 0 :: UInt256.ofNat 106 :: UInt256.ofNat 32 :: rho := by
      rfl
    have hpush : Operation.pushArity .CODECOPY = 0 := rfl
    have hpop : Operation.popArity .CODECOPY = 3 := rfl
    have hlen : (withGas pre gas).stack.length = 3 + rho.length := by
      simp [pre, preCopyState, withGas]
      omega
    have hcap : (withGas pre gas).stack.length +
        Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY := by
      omega
    have hstep := StepRunning.codecopy (withGas pre gas)
      (UInt256.ofNat 0) (UInt256.ofNat 106) (UInt256.ofNat 32) rho
      hdec hstack' hgas hcap
    have mz : (0 : Nat) % 2 ^ 256 = 0 := Nat.mod_eq_of_lt (by norm_num)
    have mz262 : (106 : Nat) % 2 ^ 256 = 106 := Nat.mod_eq_of_lt (by norm_num)
    have mz32 : (32 : Nat) % 2 ^ 256 = 32 := Nat.mod_eq_of_lt (by norm_num)
    simpa [pre, cost, preCopyState, copiedState, PrefixStateMemory.copied,
      withGas, Gas.codecopyTotal, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat, mz, mz262, mz32,
      Challenge.EvmProof.Word.succ_ofNat (n := 5037) (by norm_num),
      hcode] using hstep

#print axioms gasSteps_codecopy

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy

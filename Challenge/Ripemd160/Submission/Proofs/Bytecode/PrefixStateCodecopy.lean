import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! The first checked word is now installed with a literal `PUSH32` and one
`MSTORE`.  Three executable `JUMPDEST` bytes preserve the old instruction
indices while removing the `PUSH1`/`PUSH2`/`CODECOPY` setup. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- State before the literal first-word setup (instruction 4078, pc 4998). -/
def preCopyState (s : State) (rho : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 4998
    stack := rho }

/-- State after the literal store and width-preserving executable padding. -/
def copiedState (s : State) (rho : List UInt256) : State :=
  { PrefixStateMemory.copied s with
    pc := UInt256.ofNat 5034
    stack := rho }

/-- Gas certificate for the literal first-word setup. -/
def gasSteps_codecopy (s : State) (rho : List UInt256)
    (_hstack : rho.length ≤ 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (preCopyState s rho) (copiedState s rho) := by
  have hresult :
      Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.setupPath
        (preCopyState s rho) = some (copiedState s rho) := by
    simp (config := { maxSteps := 500000 })
      [PrefixStatePaths.setupPath,
       Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated,
       Challenge.EvmProof.Stepper.runInstr,
       preCopyState, copiedState, PrefixStateMemory.copied,
       PrefixStateMemory.literal_bytes, _hstack, hcode, hrun,
       PrefixStatePaths.pc4078, PrefixStatePaths.pc4079,
       PrefixStatePaths.pc4080, PrefixStatePaths.pc4081,
       State.activeWordsAfterUInt256,
       Challenge.EvmProof.Word.word_toNat_ofNat,
       Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.succ_ofNat_mod,
       Nat.add_assoc]
  exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka PrefixStatePaths.setupPath
    hcode hfork hresult hrun hnp

#print axioms gasSteps_codecopy

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy

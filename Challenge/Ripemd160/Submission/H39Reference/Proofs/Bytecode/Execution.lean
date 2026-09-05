import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Entry state for the universal fallback trace

The fallback proof starts after the protected entry jump and its `JUMPDEST`.
The old entry trampoline is not part of this closure.
-/

namespace Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState referenceBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3ee
      (atPC input 0x3ee) = some (mainStart input) := by
    simp [path_3ee, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, mainStart, initialState,
      Challenge.EvmProof.Word.succ_ofNat (n := 0x3ee) (by decide)]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka path_3ee
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

end Challenge.Ripemd160.Submission.H39Reference.Proofs.Bytecode.Execution

import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

/- These legacy trampoline certificates are used only by the optional gas
   development, not by the exact-bytecode correctness dependency graph. -/

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b
      (atPC input 0x1b) = some (atPC input 0x2e) := by
    simp [path_1b, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1b
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2e
      (atPC input 0x2e) = some (atPC input 0x46) := by
    simp [path_2e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_46
      (atPC input 0x46) = some (atPC input 0x5a) := by
    simp [path_46, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_46
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_5a
      (atPC input 0x5a) = some (atPC input 0x73) := by
    simp [path_5a, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_5a
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_73
      (atPC input 0x73) = some (atPC input 0x8e) := by
    simp [path_73, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_73
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_8e
      (atPC input 0x8e) = some (atPC input 0x10f) := by
    simp [path_8e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_8e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_10f
      (atPC input 0x10f) = some (atPC input 0x1b2) := by
    simp [path_10f, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_10f
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b2
      (atPC input 0x1b2) = some (atPC input 0x1db) := by
    simp [path_1b2, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1b2
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1db
      (atPC input 0x1db) = some (atPC input 0x231) := by
    simp [path_1db, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1db
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_231
      (atPC input 0x231) = some (atPC input 0x268) := by
    simp [path_231, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_231
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_268
      (atPC input 0x268) = some (atPC input 0x3c1) := by
    simp [path_268, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_268
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3c1
      (atPC input 0x3c1) = some (atPC input 0x3ee) := by
    simp [path_3c1, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_3c1
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

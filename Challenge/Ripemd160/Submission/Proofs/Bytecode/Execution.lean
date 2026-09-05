import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem helperPrefixPC16 : Artifact.submissionArtifact.instructionPC 16 = 23 := by rfl
@[simp] theorem helperPrefixPC17 : Artifact.submissionArtifact.instructionPC 17 = 24 := by rfl
@[simp] theorem helperPrefixPC18 : Artifact.submissionArtifact.instructionPC 18 = 26 := by rfl
@[simp] theorem helperPrefixPC31 : Artifact.submissionArtifact.instructionPC 31 = 41 := by rfl
@[simp] theorem helperPrefixPC32 : Artifact.submissionArtifact.instructionPC 32 = 42 := by rfl
@[simp] theorem helperPrefixPC33 : Artifact.submissionArtifact.instructionPC 33 = 44 := by rfl
@[simp] theorem helperPrefixPC45 : Artifact.submissionArtifact.instructionPC 45 = 61 := by rfl
@[simp] theorem helperPrefixPC46 : Artifact.submissionArtifact.instructionPC 46 = 62 := by rfl
@[simp] theorem helperPrefixPC47 : Artifact.submissionArtifact.instructionPC 47 = 65 := by rfl
@[simp] theorem helperPrefixPC57 : Artifact.submissionArtifact.instructionPC 57 = 78 := by rfl
@[simp] theorem helperPrefixPC58 : Artifact.submissionArtifact.instructionPC 58 = 79 := by rfl
@[simp] theorem helperPrefixPC59 : Artifact.submissionArtifact.instructionPC 59 = 82 := by rfl
@[simp] theorem helperPrefixPC71 : Artifact.submissionArtifact.instructionPC 71 = 101 := by rfl
@[simp] theorem helperPrefixPC72 : Artifact.submissionArtifact.instructionPC 72 = 102 := by rfl
@[simp] theorem helperPrefixPC73 : Artifact.submissionArtifact.instructionPC 73 = 105 := by rfl
@[simp] theorem helperPrefixPC90 : Artifact.submissionArtifact.instructionPC 90 = 125 := by rfl
@[simp] theorem helperPrefixPC91 : Artifact.submissionArtifact.instructionPC 91 = 126 := by rfl
@[simp] theorem helperPrefixPC92 : Artifact.submissionArtifact.instructionPC 92 = 129 := by rfl
@[simp] theorem helperPrefixPC190 : Artifact.submissionArtifact.instructionPC 190 = 254 := by rfl
@[simp] theorem helperPrefixPC191 : Artifact.submissionArtifact.instructionPC 191 = 255 := by rfl
@[simp] theorem helperPrefixPC192 : Artifact.submissionArtifact.instructionPC 192 = 258 := by rfl

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨16, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨17, .push ⟨1, by decide⟩ (UInt256.ofNat 0x29), by rfl, by decide⟩,
   ⟨18, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_2e : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨31, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨32, .push ⟨1, by decide⟩ (UInt256.ofNat 0x3d), by rfl, by decide⟩,
   ⟨33, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_46 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨45, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨46, .push ⟨2, by decide⟩ (UInt256.ofNat 0x4e), by rfl, by decide⟩,
   ⟨47, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_5a : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨57, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨58, .push ⟨2, by decide⟩ (UInt256.ofNat 0x65), by rfl, by decide⟩,
   ⟨59, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_73 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨71, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .push ⟨2, by decide⟩ (UInt256.ofNat 0x7d), by rfl, by decide⟩,
   ⟨73, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_8e : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨90, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨91, .push ⟨2, by decide⟩ (UInt256.ofNat 0xfe), by rfl, by decide⟩,
   ⟨92, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_10f : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨190, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨191, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b2), by rfl, by decide⟩,
   ⟨192, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b2 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨313, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨314, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1db), by rfl, by decide⟩,
   ⟨315, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1db : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨346, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 0x231), by rfl, by decide⟩,
   ⟨348, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_231 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 0x268), by rfl, by decide⟩,
   ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_268 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨448, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c1), by rfl, by decide⟩,
   ⟨450, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3c1 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨647, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨648, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨649, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0x3ee) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_start
      (atPC input 0) = some (atPC input 0x3ee) := by
    simp [path_start, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  have g : Challenge.EvmProof.GasSteps (atPC input 0) (atPC input 0x3ee) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka path_start
    · rfl
    · rfl
    · exact hrun
    · rfl
    · exact deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g rfl rfl

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x17) (atPC input 0x29) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b
      (atPC input 0x17) = some (atPC input 0x29) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0x29) (atPC input 0x3d) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2e
      (atPC input 0x29) = some (atPC input 0x3d) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0x3d) (atPC input 0x4e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_46
      (atPC input 0x3d) = some (atPC input 0x4e) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0x4e) (atPC input 0x65) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_5a
      (atPC input 0x4e) = some (atPC input 0x65) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0x65) (atPC input 0x7d) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_73
      (atPC input 0x65) = some (atPC input 0x7d) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0x7d) (atPC input 0xfe) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_8e
      (atPC input 0x7d) = some (atPC input 0xfe) := by
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
    Challenge.EvmProof.GasSteps (atPC input 0xfe) (atPC input 0x1b2) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_10f
      (atPC input 0xfe) = some (atPC input 0x1b2) := by
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

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3ee
      (atPC input 0x3ee) = some (mainStart input) := by
    simp [path_3ee, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, mainStart, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_3ee
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_entry (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  (gasSteps_start input).trans (gasSteps_3ee input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

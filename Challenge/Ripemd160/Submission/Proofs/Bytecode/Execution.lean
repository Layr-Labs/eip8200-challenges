import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

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

/-- The two division masks the artifact pushes once at the generic main entry
and keeps at the bottom of the stack for the whole run: `(2^256-1)/257` and
`(2^256-1)/65537`.  Top-first, so `mask16` sits above `mask8`. -/
def maskTail : List UInt256 :=
  [UInt256.ofNat 0x0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,
   UInt256.ofNat 0x00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff]

@[simp] theorem maskTail_length : maskTail.length = 2 := rfl

def mainStart (input : ByteArray) : State :=
  { atPC input 0x11 with stack := maskTail }

def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨0, .push ⟨1, by decide⟩ (UInt256.ofNat 180), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]


def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3, .push ⟨2, by decide⟩ (UInt256.ofNat 257), by rfl, by decide⟩,
   ⟨4, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨5, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6, .op .DIV, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨7, .push ⟨3, by decide⟩ (UInt256.ofNat 65537), by rfl, by decide⟩,
   ⟨8, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨9, .op .NOT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨10, .op .DIV, by rfl, wfOp (by decide) trivial rfl⟩]


def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0xb4) :=
  ExecutionEntry.initial_entry input

@[simp] private theorem prefixInitPc4 : Artifact.submissionArtifact.instructionPC 4 = 7 := rfl
@[simp] private theorem prefixInitPc5 : Artifact.submissionArtifact.instructionPC 5 = 8 := rfl
@[simp] private theorem prefixInitPc6 : Artifact.submissionArtifact.instructionPC 6 = 9 := rfl
@[simp] private theorem prefixInitPc8 : Artifact.submissionArtifact.instructionPC 8 = 14 := rfl
@[simp] private theorem prefixInitPc9 : Artifact.submissionArtifact.instructionPC 9 = 15 := rfl
@[simp] private theorem prefixInitPc10 : Artifact.submissionArtifact.instructionPC 10 = 16 := rfl

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3) (mainStart input) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3ee
      (atPC input 0x3) = some (mainStart input) := by
    simp [path_3ee, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, mainStart, maskTail, initialState]
    constructor <;> decide
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_3ee
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_entry (input : ByteArray)
    (entryPrefix : Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (atPC input 0x3)) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  entryPrefix.trans (gasSteps_3ee input)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

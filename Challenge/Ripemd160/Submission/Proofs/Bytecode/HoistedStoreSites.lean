import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreResearch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreSites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate
open HoistedStoreResearch

inductive Piece
  | seed | scanner | branch | success | miss | cleanup | copy

def template : Piece → List Instr
  | .seed => seedTemplate
  | .scanner => scannerTemplate
  | .branch => terminalBranch
  | .success => successTemplate
  | .miss => missTemplate
  | .cleanup => RetainedResultEdge112.cleanupTemplate
  | .copy => RetainedFallback114.copyTemplate

def index : Piece → Nat
  | .seed => 20 | .scanner => 6605 | .branch => 6758
  | .success => 6760 | .miss => 6763 | .cleanup => 6086 | .copy => 125

def pc : Piece → Nat
  | .seed => 48 | .scanner => 9709 | .branch => 9934
  | .success => 9938 | .miss => 9941 | .cleanup => 8078 | .copy => 245

theorem actual_slice (p : Piece) :
    (HoistedStoreArtifact.instructions.drop (index p)).take (template p).length = template p := by
  cases p <;> rfl

#eval IO.println "elaborating bounds"
theorem bounds (p : Piece) :
    index p + (template p).length ≤ HoistedStoreArtifact.instructions.length := by
  rw [HoistedStoreArtifact.instruction_count]
  cases p <;> decide

#eval IO.println "elaborating wellFormed"
theorem wellFormed (p : Piece) : StackRoundData.TemplateWellFormed (template p) := by
  cases p <;> decide

theorem nonempty (p : Piece) : template p ≠ [] := by cases p <;> decide

#eval IO.println "elaborating code_bound"
theorem code_bound : HoistedStoreArtifact.code.size < 2 ^ 256 := by
  rw [HoistedStoreArtifact.code_size]; decide

#eval IO.println "elaborating site"
def site (p : Piece) : GenericRoundSite HoistedStoreArtifact.artifact .Osaka (template p) :=
  StackSiteBuilder.ofSlice (template p) (index p) (actual_slice p) (bounds p)
    code_bound (StackRoundData.templateWellFormed_mem (wellFormed p)) (nonempty p)

theorem site_pc (p : Piece) : (site p).startPC = UInt256.ofNat (pc p) := by
  change UInt256.ofNat (HoistedStoreArtifact.artifact.instructionPC (index p)) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  cases p <;> decide

#eval IO.println "elaborating form"
theorem form (p : Piece) : ∀ i ∈ (template p).dropLast, RecognitionLift.Advances i := by
  apply RecognitionLift.advancesAll_sound
  cases p <;> decide

#eval IO.println "elaborating Env"
structure Env (s : State) : Prop where
  code : s.executionEnv.code = HoistedStoreArtifact.code
  fork : s.fork = .Osaka
  run : s.halt = .Running
  np : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

def lift (p : Piece) (s t : State) (e : Env s) (rho : List UInt256)
    (h : runInstrSeq (template p) {s with pc := UInt256.ofNat (pc p), stack := rho} = some t) :
    GasSteps {s with pc := UInt256.ofNat (pc p), stack := rho} t :=
  RecognitionLift.gasSteps_of_raw (site p) _ _ e.code e.fork e.run e.np
    (site_pc p).symm (form p) h

#eval IO.println "elaborating valid_scanner"
theorem valid_scanner : Decode.isValidJumpDest HoistedStoreArtifact.code 9709 = true := by
  have hp : HoistedStoreArtifact.artifact.instructionPC 6605 = 9709 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedStoreArtifact.artifact.isValidJumpDest_index 6605 (by rfl)
  rw [hp] at h; exact h

#eval IO.println "elaborating valid_miss"
theorem valid_miss : Decode.isValidJumpDest HoistedStoreArtifact.code 9941 = true := by
  have hp : HoistedStoreArtifact.artifact.instructionPC 6763 = 9941 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedStoreArtifact.artifact.isValidJumpDest_index 6763 (by rfl)
  rw [hp] at h; exact h

#eval IO.println "elaborating valid_cleanup"
theorem valid_cleanup : Decode.isValidJumpDest HoistedStoreArtifact.code 8078 = true := by
  have hp : HoistedStoreArtifact.artifact.instructionPC 6086 = 8078 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedStoreArtifact.artifact.isValidJumpDest_index 6086 (by rfl)
  rw [hp] at h; exact h

#eval IO.println "elaborating valid_generic"
theorem valid_generic : Decode.isValidJumpDest HoistedStoreArtifact.code 245 = true := by
  have hp : HoistedStoreArtifact.artifact.instructionPC 125 = 245 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedStoreArtifact.artifact.isValidJumpDest_index 125 (by rfl)
  rw [hp] at h; exact h


#print axioms actual_slice
#print axioms site_pc
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreSites

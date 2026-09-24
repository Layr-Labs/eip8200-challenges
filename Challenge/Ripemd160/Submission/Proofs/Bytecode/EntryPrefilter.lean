import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryPrefilter
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open DirectGuard

/-- A passing prefilter continues the full inherited recognizer. A nonzero result
only selects the general RIPEMD implementation; it never authorizes a digest. -/
def mask : UInt256 := UInt256.ofNat 0x108c86821c
def condition (input : ByteArray) : UInt256 :=
  UInt256.land (MachineState.readWord input 0) mask

def filterPrefix : List Located :=
  [pushAt 0 5 mask, pushAt 1 0 0, opAt 2 .CALLDATALOAD,
   opAt 3 .AND, pushAt 4 2 565]
def path : List Located := filterPrefix ++ [opAt 5 .JUMPI]
def takenPath : List Located := filterPrefix ++ [opAt 5 .JUMPI, entryDest]

private theorem pc0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc1 : Artifact.submissionArtifact.instructionPC 1 = 6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc2 : Artifact.submissionArtifact.instructionPC 2 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc3 : Artifact.submissionArtifact.instructionPC 3 = 8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc4 : Artifact.submissionArtifact.instructionPC 4 = 9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem pc5 : Artifact.submissionArtifact.instructionPC 5 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem run_prefix (input : ByteArray) :
    run filterPrefix (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 12 [565, condition input]) := by
  let w := MachineState.readWord input 0
  let l0 : Located := pushAt 0 5 mask
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 0 0 [] (by norm_num) pc0)
    (PatternedScan.stepS_push input 0 5 mask []
      (by simp) (by decide) (by decide) (by norm_num))
  let l1 : Located := pushAt 1 0 0
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 1 6 [mask] (by norm_num) pc1)
    (PatternedScan.stepS_push0 input 6 [mask] (by simp) (by norm_num))
  let l2 : Located := opAt 2 .CALLDATALOAD
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 2 7 [0, mask] (by norm_num) pc2)
    (PatternedScan.stepS_calldataload input 7 0 [mask] (by simp) (by norm_num))
  let l3 : Located := opAt 3 .AND
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 3 8 [w, mask] (by norm_num) pc3)
    (PatternedScan.stepS_and input 8 w mask [] (by simp) (by norm_num))
  let l4 : Located := pushAt 4 2 565
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4 9 [condition input] (by norm_num) pc4)
    (PatternedScan.stepS_push input 9 2 565 [condition input]
      (by simp) (by decide) (by decide) (by norm_num))
  have h01 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have h012 := DataStepper.runLocatedBlock_append [l0,l1] [l2] _ _ _ h01 rfl h2
  have h0123 := DataStepper.runLocatedBlock_append [l0,l1,l2] [l3] _ _ _ h012 rfl h3
  exact DataStepper.runLocatedBlock_append [l0,l1,l2,l3] [l4] _ _ _ h0123 rfl h4

theorem run_fall (input : ByteArray) (h : condition input = 0) :
    run path (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 13 []) := by
  have hp := run_prefix input
  rw [h] at hp
  have hj := PatternedScan.blockOfS (opAt 5 .JUMPI)
    (PatternedScan.pcFactS input 5 12 [565, 0] (by norm_num) pc5)
    (PatternedScan.stepS_jumpi_fall input 12 565 0 []
      (by simp) (by norm_num) (by decide))
  exact DataStepper.runLocatedBlock_append filterPrefix [opAt 5 .JUMPI] _ _ _ hp rfl hj

theorem run_taken (input : ByteArray) (h : condition input ≠ 0) :
    run takenPath (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 566 []) := by
  have hp := run_prefix input
  have hj := PatternedScan.blockOfS (opAt 5 .JUMPI)
    (PatternedScan.pcFactS input 5 12 [565, condition input] (by norm_num) pc5)
    (PatternedScan.stepS_jumpi_taken input 12 565 565 (condition input) []
      (by simp) (by norm_num) (by rfl)
      (by
        intro hz
        apply h
        rw [Word.word_eq_ofNat_toNat (condition input), hz]
        rfl) generic_dest)
  have hd : DataStepper.runLocatedBlock [entryDest] (PatternedScan.stS input 565 []) =
      some (PatternedScan.stS input 566 []) := by
    exact PatternedScan.blockOfS entryDest
      (PatternedScan.pcFactS input 303 565 [] (by norm_num)
        (by rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (PatternedScan.stepS_jumpdest input 565 [] (by simp) (by norm_num))
  have hje := DataStepper.runLocatedBlock_append [opAt 5 .JUMPI] [entryDest]
    _ _ _ hj rfl hd
  exact DataStepper.runLocatedBlock_append filterPrefix [opAt 5 .JUMPI, entryDest]
    _ _ _ hp rfl hje

def gasSteps_fall (input : ByteArray) (h : condition input = 0) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 13) :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path rfl rfl (run_fall input h) rfl deployAddress_not_precompile

def gasSteps_taken (input : ByteArray) (h : condition input ≠ 0) :
    GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 566) :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    takenPath rfl rfl (run_taken input h) rfl deployAddress_not_precompile

theorem condition_empty : condition ByteArray.empty = 0 := by
  have hz : MachineState.readWord ByteArray.empty 0 = 0 := by
    unfold MachineState.readWord
    rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
      YulEvmCompiler.ByteArray.toList_eq_data]
    decide
  rw [condition, hz]
  decide

theorem positive_of_taken (input : ByteArray) (h : condition input ≠ 0) :
    0 < input.size := by
  by_contra hn
  have he := TinyGuardLogic.input_eq_empty input (by omega)
  rw [he] at h
  exact h condition_empty

theorem condition_of_fullWord (input : ByteArray)
    (h : MachineState.readWord input 0 = KnownInputData.fullWord) : condition input = 0 := by
  rw [condition, h]
  decide

#print axioms gasSteps_fall
#print axioms gasSteps_taken
end Challenge.Ripemd160.Submission.Proofs.Bytecode.EntryPrefilter

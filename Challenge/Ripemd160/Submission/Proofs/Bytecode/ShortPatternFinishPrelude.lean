import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest32
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest31
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest55
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest64
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest65
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Codecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest119
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned63Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScanDigest128
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternDigest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Scan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Cleanup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def paddedDigestWord (n : Nat) : UInt256 :=
  if n = 1 then ScanDigest1.paddedDigestWord else
  if n = 31 then ScanDigest31.paddedDigestWord else
  if n = 32 then ScanDigest32.paddedDigestWord else
  if n = 55 then ScanDigest55.paddedDigestWord else
  if n = 256 then Patterned256Digest.paddedDigestWord else
  if n = 376 then Prefix256Digest.paddedDigestWord else
  if n = 1000 then PatternedDigest.paddedDigestWord else
  if n = 56 then 0xd8e2e84bad19fc85dbadb55fa5467631ce141503 else
  if n = 120 then 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc else
  if n = 64 then 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817 else
  if n = 65 then 0x475272ba467ca6716dbb1c19a84de355f065829a else
  if n = 128 then 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179 else
  if n = 63 then 0x37880ee5e2e821e0540bb146e33b37342316e7ed else
  0x2b9567d684dc89cd54620e46029f5bda0ecab787

def paddedDigest (n : Nat) : ByteArray :=
  if n = 1 then ScanDigest1.paddedDigest else
  if n = 31 then ScanDigest31.paddedDigest else
  if n = 32 then ScanDigest32.paddedDigest else
  if n = 55 then ScanDigest55.paddedDigest else
  if n = 256 then Patterned256Digest.paddedDigest else
  if n = 376 then Prefix256Digest.paddedDigest else
  if n = 1000 then PatternedDigest.paddedDigest else
  if n = 56 then ShortPatternDigest.paddedDigest56 else
  if n = 120 then ShortPatternDigest.paddedDigest120 else
  if n = 64 then ScanDigest64.paddedDigest else
  if n = 65 then ScanDigest65.paddedDigest else
  if n = 128 then ScanDigest128.paddedDigest else
  if n = 63 then Patterned63Digest.paddedDigest else
  ScanDigest119.paddedDigest

def answerMemory (n : Nat) : ByteArray := storeWord ByteArray.empty 0 (paddedDigestWord n)

def returnRest (sv ov : UInt256) : List UInt256 :=
  [sv, ov, 0, P7, M, m7, P, m8]

def selectorState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 4832 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 4832 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 4854 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 4855
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 4856
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory n) 0 32 }

@[simp] theorem paddedDigest_size (n : Nat) : (paddedDigest n).size = 32 := by
  simp only [paddedDigest, apply_ite ByteArray.size,
    show ScanDigest1.paddedDigest.size = 32 from rfl,
    show ScanDigest31.paddedDigest.size = 32 from rfl,
    show ScanDigest32.paddedDigest.size = 32 from rfl,
    show ScanDigest55.paddedDigest.size = 32 from rfl,
    show Patterned256Digest.paddedDigest.size = 32 from rfl,
    show Prefix256Digest.paddedDigest.size = 32 from rfl,
    show PatternedDigest.paddedDigest.size = 32 from rfl,
    show ShortPatternDigest.paddedDigest56.size = 32 from rfl,
    show ShortPatternDigest.paddedDigest120.size = 32 from rfl,
    show ScanDigest64.paddedDigest.size = 32 from rfl,
    show ScanDigest65.paddedDigest.size = 32 from rfl,
    show ScanDigest128.paddedDigest.size = 32 from rfl,
    show Patterned63Digest.paddedDigest.size = 32 from rfl,
    show ScanDigest119.paddedDigest.size = 32 from rfl,
    ite_self]

theorem wordBytes_eq_paddedDigest (n : Nat) :
    Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32 = paddedDigest n := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  by_cases h1 : n = 1
  · subst n
    decide
  by_cases h31 : n = 31
  · subst n
    decide
  by_cases h32 : n = 32
  · subst n
    decide
  by_cases h55 : n = 55
  · subst n
    decide
  by_cases h256 : n = 256
  · subst n
    decide
  by_cases h376 : n = 376
  · subst n
    decide
  by_cases h1000 : n = 1000
  · subst n
    decide
  by_cases h56 : n = 56
  · subst n
    decide
  by_cases h120 : n = 120
  · subst n
    decide
  by_cases h64 : n = 64
  · subst n
    decide
  by_cases h65 : n = 65
  · subst n
    decide
  by_cases h128 : n = 128
  · subst n
    decide
  by_cases h63 : n = 63
  · subst n
    decide
  simp only [paddedDigestWord, paddedDigest, if_neg h1, if_neg h31, if_neg h32, if_neg h55, if_neg h256, if_neg h376, if_neg h1000, if_neg h56, if_neg h120, if_neg h64, if_neg h65, if_neg h128, if_neg h63]
  decide

theorem answerMemory_read (n : Nat) :
    MachineState.readPadded (answerMemory n) 0 32 = paddedDigest n := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (n : Nat) (input : ByteArray) (sv ov : UInt256) :
    (returnedState n input sv ov).hReturn = paddedDigest n := answerMemory_read n

def tableOffset (n : Nat) : Nat := 4858 + 21 * ((2377101 / n) % 16)
def copyReadyState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 4853 ([12, UInt256.ofNat (tableOffset n), 20] ++ returnRest sv ov)

def quotientState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 4843 ([UInt256.div (UInt256.ofNat 2377101) (UInt256.ofNat n), 15, 20] ++ returnRest sv ov)

def tableMemory (n : Nat) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (MachineState.readPadded submissionBytecode (tableOffset n) 20) 12
private theorem readPadded_append_right (a b : ByteArray) (start n : Nat)
    (hstart : a.size ≤ start) :
    MachineState.readPadded (a ++ b) start n =
      MachineState.readPadded b (start - a.size) n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hia hib
    rw [← Memory.getD0_eq_getElem _ _ hia, ← Memory.getD0_eq_getElem _ _ hib,
      Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    have hi : i < n := by simpa using hia
    rw [if_pos hi, if_pos hi, Memory.getElem?_getD_append, if_neg (by omega)]
    congr 2
    omega

private def codePrefix : ByteArray :=
  submissionByteChunk0
 ++   submissionByteChunk1
 ++   submissionByteChunk2
 ++   submissionByteChunk3
 ++   submissionByteChunk4
 ++   submissionByteChunk5
 ++   submissionByteChunk6
 ++   submissionByteChunk7
 ++   submissionByteChunk8
 ++   submissionByteChunk9
 ++   submissionByteChunk10
 ++   submissionByteChunk11
 ++   submissionByteChunk12
 ++   submissionByteChunk13
 ++   submissionByteChunk14
 ++   submissionByteChunk15
 ++   submissionByteChunk16
 ++   submissionByteChunk17
 ++   submissionByteChunk18
 ++   submissionByteChunk19
private theorem codePrefix_size : codePrefix.size = 4736 := by
  simp only [codePrefix, ByteArray.size_append,
    submissionByteChunk0_size,
    submissionByteChunk1_size,
    submissionByteChunk2_size,
    submissionByteChunk3_size,
    submissionByteChunk4_size,
    submissionByteChunk5_size,
    submissionByteChunk6_size,
    submissionByteChunk7_size,
    submissionByteChunk8_size,
    submissionByteChunk9_size,
    submissionByteChunk10_size,
    submissionByteChunk11_size,
    submissionByteChunk12_size,
    submissionByteChunk13_size,
    submissionByteChunk14_size,
    submissionByteChunk15_size,
    submissionByteChunk16_size,
    submissionByteChunk17_size,
    submissionByteChunk18_size,
    submissionByteChunk19_size]
private theorem code_split : submissionBytecode = codePrefix ++ submissionByteChunk20 := rfl
private theorem tableRead (n : Nat) :
    MachineState.readPadded submissionBytecode (tableOffset n) 20 =
      MachineState.readPadded submissionByteChunk20 (122 + 21 * ((2377101 / n) % 16)) 20 := by
  rw [code_split, readPadded_append_right _ _ _ _ (by rw [codePrefix_size]; unfold tableOffset; omega), codePrefix_size]
  congr 1
  unfold tableOffset
  omega

private theorem tablePayload (n : Nat)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) :
    MachineState.readPadded submissionByteChunk20 (122 + 21 * ((2377101 / n) % 16)) 20 =
      (paddedDigest n).extract 12 32 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem tableMemory_eq (n : Nat) (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119 ∨ n = 55 ∨ n = 256 ∨ n = 376 ∨ n = 1000 ∨ n = 1 ∨ n = 31 ∨ n = 32) :
    tableMemory n = answerMemory n := by
  unfold tableMemory
  rw [tableRead, tablePayload n hn]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold answerMemory storeWord
    rw [Memory.natToBytesPadded_eq_natToBE]
    unfold MachineState.writeBytes
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

def selectorPath : List Located := []

def digestStorePrePath : List Located :=
  [ opAt 4052 .JUMPDEST,
    pushAt 4053 1 20,
    pushAt 4054 1 15,
    opAt 4055 .CALLDATASIZE,
    pushAt 4056 3 2377101,
    opAt 4057 .DIV ]

def digestStorePostPath : List Located :=
  [ opAt 4058 .AND,
    pushAt 4059 1 21,
    opAt 4060 .MUL,
    pushAt 4061 2 4858,
    opAt 4062 .ADD,
    pushAt 4063 1 12]

def digestFinishPath : List Located :=
  [pushAt 4066 0 0, opAt 4067 .RETURN]

@[simp] theorem pcE2Length : Artifact.submissionArtifact.instructionPC 4053 = 4833 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

@[simp] theorem pc4843 : Artifact.submissionArtifact.instructionPC 4052 = 4832 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4844 : Artifact.submissionArtifact.instructionPC 4054 = 4835 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4846 : Artifact.submissionArtifact.instructionPC 4055 = 4837 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4847 : Artifact.submissionArtifact.instructionPC 4056 = 4838 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4850 : Artifact.submissionArtifact.instructionPC 4057 = 4842 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4851 : Artifact.submissionArtifact.instructionPC 4058 = 4843 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4853 : Artifact.submissionArtifact.instructionPC 4058 = 4843 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4854 : Artifact.submissionArtifact.instructionPC 4058 = 4843 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4856 : Artifact.submissionArtifact.instructionPC 4058 = 4843 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4857 : Artifact.submissionArtifact.instructionPC 4058 = 4843 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4858 : Artifact.submissionArtifact.instructionPC 4059 = 4844 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4860 : Artifact.submissionArtifact.instructionPC 4060 = 4846 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4861 : Artifact.submissionArtifact.instructionPC 4061 = 4847 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4864 : Artifact.submissionArtifact.instructionPC 4062 = 4850 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4865 : Artifact.submissionArtifact.instructionPC 4063 = 4851 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4867 : Artifact.submissionArtifact.instructionPC 4063 = 4851 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4868 : Artifact.submissionArtifact.instructionPC 4063 = 4851 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4870 : Artifact.submissionArtifact.instructionPC 4064 = 4853 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4871 : Artifact.submissionArtifact.instructionPC 4065 = 4854 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4872 : Artifact.submissionArtifact.instructionPC 4066 = 4855 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc4873 : Artifact.submissionArtifact.instructionPC 4067 = 4856 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

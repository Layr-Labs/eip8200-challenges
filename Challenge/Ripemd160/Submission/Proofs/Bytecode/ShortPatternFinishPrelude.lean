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
  if n = 56 then 0xd8e2e84bad19fc85dbadb55fa5467631ce141503 else
  if n = 120 then 0x4de20b6b1fb2af442370c40e53a50aca360fc3bc else
  if n = 64 then 0x8a14b0c89287b39b1a2f73aa79a1ce95b04e7817 else
  if n = 65 then 0x475272ba467ca6716dbb1c19a84de355f065829a else
  if n = 128 then 0x28dfaf14ed9953f49c7abb561308d0c64bc4c179 else
  if n = 63 then 0x37880ee5e2e821e0540bb146e33b37342316e7ed else
  0x2b9567d684dc89cd54620e46029f5bda0ecab787

def paddedDigest (n : Nat) : ByteArray :=
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
  stS input 255 (returnRest sv ov)

def digestEntryState (_n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5072 (returnRest sv ov)

def storedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { stS input 5096 (returnRest sv ov) with
    memory := answerMemory n
    activeWords := UInt256.ofNat 1 }

def sizedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5097
    stack := UInt256.ofNat 32 :: returnRest sv ov }

def returnedState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  { storedState n input sv ov with
    pc := UInt256.ofNat 5098
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory n) 0 32 }

@[simp] theorem paddedDigest_size (n : Nat) : (paddedDigest n).size = 32 := by
  unfold paddedDigest
  split_ifs <;> decide

theorem wordBytes_eq_paddedDigest (n : Nat) :
    Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32 = paddedDigest n := by
  rw [Memory.natToBytesPadded_eq_natToBE]
  unfold paddedDigestWord paddedDigest
  split_ifs <;> decide

theorem answerMemory_read (n : Nat) :
    MachineState.readPadded (answerMemory n) 0 32 = paddedDigest n := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded (paddedDigestWord n).toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    wordBytes_eq_paddedDigest, paddedDigest_size] using h

@[simp] theorem returnedState_hReturn (n : Nat) (input : ByteArray) (sv ov : UInt256) :
    (returnedState n input sv ov).hReturn = paddedDigest n := answerMemory_read n

def tableOffset (n : Nat) : Nat := 5100 + 21 * (((19 * n) / 16) % 7)
def copyReadyState (n : Nat) (input : ByteArray) (sv ov : UInt256) : State :=
  stS input 5095 ([12, UInt256.ofNat (tableOffset n), 20] ++ returnRest sv ov)

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
private theorem codePrefix_size : codePrefix.size = 4926 := by
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
      MachineState.readPadded submissionByteChunk20 (174 + 21 * (((19 * n) / 16) % 7)) 20 := by
  rw [code_split, readPadded_append_right _ _ _ _ (by rw [codePrefix_size]; unfold tableOffset; omega), codePrefix_size]
  congr 1
  unfold tableOffset
  omega

private theorem tablePayload (n : Nat)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119) :
    MachineState.readPadded submissionByteChunk20 (174 + 21 * (((19 * n) / 16) % 7)) 20 =
      (paddedDigest n).extract 12 32 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem tableMemory_eq (n : Nat) (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119) :
    tableMemory n = answerMemory n := by
  unfold tableMemory
  rw [tableRead, tablePayload n hn]
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold answerMemory storeWord
    rw [Memory.natToBytesPadded_eq_natToBE]
    unfold MachineState.writeBytes
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
      List.forIn_pure_yield_eq_foldl, Id.run_pure]
    decide

def selectorPath : List Located :=
  [opAt 162 .CALLDATASIZE,
   pushAt 163 1 129,
   opAt 164 .GT,
   pushAt 165 2 5072,
   opAt 166 .JUMPI]

def digestStorePath : List Located :=
  [opAt 4102 .JUMPDEST,
   pushAt 4103 1 7,
   opAt 4104 .CALLDATASIZE,
   pushAt 4105 1 19,
   opAt 4106 .MUL,
   pushAt 4107 1 4,
   opAt 4108 .SHR,
   opAt 4109 .MOD,
   pushAt 4110 1 21,
   opAt 4111 .MUL,
   pushAt 4112 2 5100,
   opAt 4113 .ADD,
   pushAt 4114 1 20,
   opAt 4115 (.Swap ⟨0, by decide⟩),
   pushAt 4116 1 12]

def digestFinishPath : List Located :=
  [pushAt 4119 0 0,
   opAt 4120 .RETURN]

@[simp] theorem pc255 : Artifact.submissionArtifact.instructionPC 162 = 255 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc256 : Artifact.submissionArtifact.instructionPC 163 = 256 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc258 : Artifact.submissionArtifact.instructionPC 164 = 258 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc259 : Artifact.submissionArtifact.instructionPC 165 = 259 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc262 : Artifact.submissionArtifact.instructionPC 166 = 262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5072 : Artifact.submissionArtifact.instructionPC 4102 = 5072 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5073 : Artifact.submissionArtifact.instructionPC 4103 = 5073 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5075 : Artifact.submissionArtifact.instructionPC 4104 = 5075 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5076 : Artifact.submissionArtifact.instructionPC 4105 = 5076 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5078 : Artifact.submissionArtifact.instructionPC 4106 = 5078 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5079 : Artifact.submissionArtifact.instructionPC 4107 = 5079 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5081 : Artifact.submissionArtifact.instructionPC 4108 = 5081 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5082 : Artifact.submissionArtifact.instructionPC 4109 = 5082 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5083 : Artifact.submissionArtifact.instructionPC 4110 = 5083 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5085 : Artifact.submissionArtifact.instructionPC 4111 = 5085 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5086 : Artifact.submissionArtifact.instructionPC 4112 = 5086 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5089 : Artifact.submissionArtifact.instructionPC 4113 = 5089 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5090 : Artifact.submissionArtifact.instructionPC 4114 = 5090 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5092 : Artifact.submissionArtifact.instructionPC 4115 = 5092 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5093 : Artifact.submissionArtifact.instructionPC 4116 = 5093 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5095 : Artifact.submissionArtifact.instructionPC 4117 = 5095 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5096 : Artifact.submissionArtifact.instructionPC 4118 = 5096 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5097 : Artifact.submissionArtifact.instructionPC 4119 = 5097 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] theorem pc5098 : Artifact.submissionArtifact.instructionPC 4120 = 5098 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem run_selector (n : Nat) (input : ByteArray) (sv ov : UInt256)
    (hn : n = 56 ∨ n = 120 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 63 ∨ n = 119) (hsize : input.size = n) :
    run selectorPath (selectorState n input sv ov) =
      some (digestEntryState n input sv ov) := by
  change run selectorPath (stS input 255 (returnRest sv ov)) =
    some (stS input 5072 (returnRest sv ov))
  have hdest : Decode.isValidJumpDest submissionBytecode 5072 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4102 (by rfl)
  have htrue : UInt256.isTrue (UInt256.gt 129 (UInt256.ofNat input.size)) := by
    rw [hsize]
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have h0 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .CALLDATASIZE]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 162 255 _ (by norm_num) pc255)
      (stepS_calldatasize input 255 (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h1 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 163 1 129]
          (stS input 256 (UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 163 256 _ (by norm_num) pc256)
      (stepS_push input 256 1 129
        (UInt256.ofNat input.size :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h2 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 164 .GT]
          (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) =
        some (stS input 259
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 164 258 _ (by norm_num) pc258)
      (stepS_gt input 258 129 (UInt256.ofNat input.size) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num))
  have h3 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [pushAt 165 2 5072]
          (stS input 259
            (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 262
          (5072 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 165 259 _ (by norm_num) pc259)
      (stepS_push input 259 2 5072
        (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)
        (by simp [returnRest]) (by decide) (by decide) (by norm_num))
  have h4 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 166 .JUMPI]
          (stS input 262
            (5072 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) =
        some (stS input 5072 (returnRest sv ov)) := by
    exact blockOfS _
      (pcFactS input 166 262 _ (by norm_num) pc262)
      (stepS_jumpi_taken input 262 5072 5072
        (UInt256.gt 129 (UInt256.ofNat input.size)) (returnRest sv ov)
        (by simp [returnRest]) (by norm_num) rfl htrue hdest)
  have h01 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .CALLDATASIZE, pushAt 163 1 129]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 258 (129 :: UInt256.ofNat input.size :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 162 .CALLDATASIZE] [pushAt 163 1 129]
      _ _ _ h0 (by rfl) h1
  have h012 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .CALLDATASIZE, pushAt 163 1 129, opAt 164 .GT]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 259
          (UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 162 .CALLDATASIZE, pushAt 163 1 129] [opAt 164 .GT]
      _ _ _ h01 (by rfl) h2
  have h0123 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .CALLDATASIZE, pushAt 163 1 129, opAt 164 .GT,
            pushAt 165 2 5072]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 262
          (5072 :: UInt256.gt 129 (UInt256.ofNat input.size) :: returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 162 .CALLDATASIZE, pushAt 163 1 129, opAt 164 .GT]
      [pushAt 165 2 5072] _ _ _ h012 (by rfl) h3
  have h01234 :
      Challenge.EvmProof.Stepper.runLocatedBlock
          [opAt 162 .CALLDATASIZE, pushAt 163 1 129, opAt 164 .GT,
            pushAt 165 2 5072, opAt 166 .JUMPI]
          (stS input 255 (returnRest sv ov)) =
        some (stS input 5072 (returnRest sv ov)) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 162 .CALLDATASIZE, pushAt 163 1 129, opAt 164 .GT,
        pushAt 165 2 5072] [opAt 166 .JUMPI] _ _ _ h0123 (by rfl) h4
  simpa only [selectorPath] using h01234


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternFinish

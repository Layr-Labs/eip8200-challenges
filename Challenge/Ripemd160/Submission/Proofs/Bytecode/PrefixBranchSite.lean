import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixCalldata
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# `Located` certificate for the appended H1 branch

The 37 appended instructions occupy indices `4575..4611` (PC `5363..5503`).
This module is the certificate and the `runLocatedBlock` run; it states no
mathematics -- `PrefixStateData.h8_firstBlock` supplies that, and
`PrefixCalldata.branchCondition_eq_zero_iff` ties the `JUMPI` condition, in the
stack order the bytecode produces, to `PrefixBranch.Recognised`.

The path is split at the two `JUMPI`s because `runLocatedBlock` requires each
entry's `instructionPC` to match the running `pc`: a fall-through continues into
the next segment, a taken branch continues into `fallbackPath`.  Every `Located`
is built by `PatternedScan.opAt` / `pushAt`, whose obligations discharge by
`rfl` / `decide` against this tree's own `Artifact.submissionInstructions`.

`calldata = input` is a *premise* throughout, as the provider binds it.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranchSite

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

def guardPath : List Located :=
  [opAt 4575 .JUMPDEST,
   pushAt 4576 1 64,
   opAt 4577 .CALLDATASIZE,
   opAt 4578 .LT,
   pushAt 4579 2 5499,
   opAt 4580 .JUMPI]

def comparePath : List Located :=
  [pushAt 4581 0 0,
   opAt 4582 .CALLDATALOAD,
   pushAt 4583 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 4584 .XOR,
   pushAt 4585 1 32,
   opAt 4586 .CALLDATALOAD,
   pushAt 4587 32 75898346434861812577553744355519055536350986179947755549958789636940356975906,
   opAt 4588 .XOR,
   opAt 4589 .OR,
   pushAt 4590 2 5499,
   opAt 4591 .JUMPI]

def storePath : List Located :=
  [pushAt 4592 4 1080717082,
   pushAt 4593 2 352,
   opAt 4594 .MSTORE,
   pushAt 4595 4 2391128076,
   pushAt 4596 2 384,
   opAt 4597 .MSTORE,
   pushAt 4598 4 621343384,
   pushAt 4599 2 416,
   opAt 4600 .MSTORE,
   pushAt 4601 4 220066081,
   pushAt 4602 2 448,
   opAt 4603 .MSTORE,
   pushAt 4604 4 1007308478,
   pushAt 4605 2 480,
   opAt 4606 .MSTORE,
   pushAt 4607 2 466,
   opAt 4608 .JUMP]

def fallbackPath : List Located :=
  [opAt 4609 .JUMPDEST,
   pushAt 4610 2 477,
   opAt 4611 .JUMP]

/-- The whole appended branch as one certificate: 37 `Located`s covering
indices `4575..4611`. -/
def branchPath : List Located :=
  guardPath ++ comparePath ++ storePath ++ fallbackPath

@[simp] theorem branchPath_length : branchPath.length = 37 := by rfl

@[simp] theorem guardPath_length : guardPath.length = 6 := by rfl
@[simp] theorem comparePath_length : comparePath.length = 11 := by rfl
@[simp] theorem storePath_length : storePath.length = 17 := by rfl
@[simp] theorem fallbackPath_length : fallbackPath.length = 3 := by rfl

/-- The certificate carries exactly the instructions of `PrefixBranch.branchTemplate`.
This is the join between the certificate and the template that was checked
shape-for-shape against `Artifact.lean`. -/
theorem branchPath_instructions :
    branchPath.map (fun l => l.instruction) = PrefixBranch.branchTemplate := by
  rfl

/-- Each certificate entry sits at the index it claims. -/
theorem branchPath_indices :
    branchPath.map (fun l => l.index) = List.range' 4575 37 := by
  rfl


/-! ## Program counters of the appended block

One fact per index, so a stale PC fails at its own line rather than inside a
large `simp`. -/

private theorem pc4575 : Artifact.submissionArtifact.instructionPC 4575 = 5363 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4576 : Artifact.submissionArtifact.instructionPC 4576 = 5364 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4577 : Artifact.submissionArtifact.instructionPC 4577 = 5366 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4578 : Artifact.submissionArtifact.instructionPC 4578 = 5367 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4579 : Artifact.submissionArtifact.instructionPC 4579 = 5368 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4580 : Artifact.submissionArtifact.instructionPC 4580 = 5371 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4581 : Artifact.submissionArtifact.instructionPC 4581 = 5372 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4582 : Artifact.submissionArtifact.instructionPC 4582 = 5373 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4583 : Artifact.submissionArtifact.instructionPC 4583 = 5374 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4584 : Artifact.submissionArtifact.instructionPC 4584 = 5407 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4585 : Artifact.submissionArtifact.instructionPC 4585 = 5408 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4586 : Artifact.submissionArtifact.instructionPC 4586 = 5410 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4587 : Artifact.submissionArtifact.instructionPC 4587 = 5411 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4588 : Artifact.submissionArtifact.instructionPC 4588 = 5444 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4589 : Artifact.submissionArtifact.instructionPC 4589 = 5445 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4590 : Artifact.submissionArtifact.instructionPC 4590 = 5446 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4591 : Artifact.submissionArtifact.instructionPC 4591 = 5449 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4592 : Artifact.submissionArtifact.instructionPC 4592 = 5450 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4593 : Artifact.submissionArtifact.instructionPC 4593 = 5455 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4594 : Artifact.submissionArtifact.instructionPC 4594 = 5458 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4595 : Artifact.submissionArtifact.instructionPC 4595 = 5459 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4596 : Artifact.submissionArtifact.instructionPC 4596 = 5464 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4597 : Artifact.submissionArtifact.instructionPC 4597 = 5467 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4598 : Artifact.submissionArtifact.instructionPC 4598 = 5468 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4599 : Artifact.submissionArtifact.instructionPC 4599 = 5473 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4600 : Artifact.submissionArtifact.instructionPC 4600 = 5476 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4601 : Artifact.submissionArtifact.instructionPC 4601 = 5477 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4602 : Artifact.submissionArtifact.instructionPC 4602 = 5482 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4603 : Artifact.submissionArtifact.instructionPC 4603 = 5485 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4604 : Artifact.submissionArtifact.instructionPC 4604 = 5486 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4605 : Artifact.submissionArtifact.instructionPC 4605 = 5491 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4606 : Artifact.submissionArtifact.instructionPC 4606 = 5494 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4607 : Artifact.submissionArtifact.instructionPC 4607 = 5495 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4608 : Artifact.submissionArtifact.instructionPC 4608 = 5498 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4609 : Artifact.submissionArtifact.instructionPC 4609 = 5499 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4610 : Artifact.submissionArtifact.instructionPC 4610 = 5500 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl
private theorem pc4611 : Artifact.submissionArtifact.instructionPC 4611 = 5503 := by
  rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

/-! ## Memory effect of the five stores -/

/-- Growth caused by one 32-byte store, in the shape `FastOutputTrace` uses. -/
def storeActive (current : UInt256) (address : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter current.toNat address 32)

/-- Active words after the five ascending stores at `352..480`. -/
def storeActive5 (current : UInt256) : UInt256 :=
  storeActive (storeActive (storeActive (storeActive
    (storeActive current 352) 384) 416) 448) 480

/-- The state the store segment produces: `H1` in `352..480`, `pc` at the driver
loop head, stack unchanged (the segment's net stack effect is zero). -/
def afterStores (s : State) : State :=
  { s with
    pc := UInt256.ofNat PrefixBranch.loopHeadPC
    memory := PrefixBranch.branchMemory s.memory
    activeWords := storeActive5 s.activeWords }

/-! ## The runs

Each segment is stated on a generic running state `s` whose `pc` is the
segment's entry, so the segments compose and none of them assumes the branch is
entered from `initialState`.  `hcalldata` is a premise, never discharged here. -/

/-- Fall-out: `JUMPDEST ; PUSH2 477 ; JUMP` returns to the original first-block
body.  Stack unchanged. -/
theorem run_fallback (s : State) (rest : List UInt256)
    (hpc : s.pc = UInt256.ofNat 5499) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 1 < 1024)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    run fallbackPath s =
      some { s with pc := UInt256.ofNat PrefixBranch.originalBodyPC } := by
  have hc0 : rest.length < 1024 := by omega
  have hd477 : Decode.isValidJumpDest Artifact.submissionArtifact.code 477 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 271 (by rfl)
  have w5499 : (UInt256.ofNat 5499).add (UInt256.ofNat 1) = UInt256.ofNat 5500 := by
    show UInt256.ofNat 5499 + UInt256.ofNat 1 = UInt256.ofNat 5500
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5500 : UInt256.ofNat 5500 + UInt256.ofNat 3 = UInt256.ofNat 5503 := by
    show UInt256.ofNat 5500 + UInt256.ofNat 3 = UInt256.ofNat 5503
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [fallbackPath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4609, pc4610, pc4611,
    hpc, hstack, hrun, PrefixBranch.originalBodyPC,
    hlen, hc0,
    w5499, w5500,
    hcode, hd477,
    Challenge.EvmProof.Word.literal_eq_ofNat]


/-- Size guard, fall-through: an input of at least 64 bytes continues into the
comparisons. -/
theorem run_guard_fall (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5363) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 2 < 1024)
    (hfit : CalldataFits input)
    (hsize : ¬ input.size < 64) :
    run guardPath s = some { s with pc := UInt256.ofNat 5372 } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hsize256 : input.size < 2 ^ 256 := by
    have hsize64 : input.size < 2 ^ 64 := hfit
    exact lt_trans hsize64 (by norm_num)
  have hguard :
      UInt256.lt (UInt256.ofNat input.size) (UInt256.ofNat 64) = UInt256.ofNat 0 := by
    simp [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hsize256, hsize]
  have w5363 : (UInt256.ofNat 5363).add (UInt256.ofNat 1) = UInt256.ofNat 5364 := by
    show UInt256.ofNat 5363 + UInt256.ofNat 1 = UInt256.ofNat 5364
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5364 : UInt256.ofNat 5364 + UInt256.ofNat 2 = UInt256.ofNat 5366 := by
    show UInt256.ofNat 5364 + UInt256.ofNat 2 = UInt256.ofNat 5366
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5366 : (UInt256.ofNat 5366).add (UInt256.ofNat 1) = UInt256.ofNat 5367 := by
    show UInt256.ofNat 5366 + UInt256.ofNat 1 = UInt256.ofNat 5367
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5367 : (UInt256.ofNat 5367).add (UInt256.ofNat 1) = UInt256.ofNat 5368 := by
    show UInt256.ofNat 5367 + UInt256.ofNat 1 = UInt256.ofNat 5368
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5368 : UInt256.ofNat 5368 + UInt256.ofNat 3 = UInt256.ofNat 5371 := by
    show UInt256.ofNat 5368 + UInt256.ofNat 3 = UInt256.ofNat 5371
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5371 : (UInt256.ofNat 5371).add (UInt256.ofNat 1) = UInt256.ofNat 5372 := by
    show UInt256.ofNat 5371 + UInt256.ofNat 1 = UInt256.ofNat 5372
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [guardPath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4575, pc4576, pc4577, pc4578, pc4579, pc4580,
    hpc, hstack, hrun, hcalldata, hsize,
    hlen, hc0, hc1, hguard,
    w5363, w5364, w5366, w5367, w5368, w5371]


/-- Size guard, taken: a short input falls out to `5499`. -/
theorem run_guard_taken (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5363) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 2 < 1024)
    (hsize : input.size < 64)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    run guardPath s = some { s with pc := UInt256.ofNat 5499 } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hd5499 : Decode.isValidJumpDest Artifact.submissionArtifact.code 5499 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4609 (by rfl)
  have w5363 : (UInt256.ofNat 5363).add (UInt256.ofNat 1) = UInt256.ofNat 5364 := by
    show UInt256.ofNat 5363 + UInt256.ofNat 1 = UInt256.ofNat 5364
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5364 : UInt256.ofNat 5364 + UInt256.ofNat 2 = UInt256.ofNat 5366 := by
    show UInt256.ofNat 5364 + UInt256.ofNat 2 = UInt256.ofNat 5366
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5366 : (UInt256.ofNat 5366).add (UInt256.ofNat 1) = UInt256.ofNat 5367 := by
    show UInt256.ofNat 5366 + UInt256.ofNat 1 = UInt256.ofNat 5367
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5367 : (UInt256.ofNat 5367).add (UInt256.ofNat 1) = UInt256.ofNat 5368 := by
    show UInt256.ofNat 5367 + UInt256.ofNat 1 = UInt256.ofNat 5368
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5368 : UInt256.ofNat 5368 + UInt256.ofNat 3 = UInt256.ofNat 5371 := by
    show UInt256.ofNat 5368 + UInt256.ofNat 3 = UInt256.ofNat 5371
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [guardPath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4575, pc4576, pc4577, pc4578, pc4579, pc4580,
    hpc, hstack, hrun, hcalldata, hsize,
    hlen, hc0, hc1,
    w5363, w5364, w5366, w5367, w5368,
    hcode, hd5499,
    Challenge.EvmProof.Word.literal_eq_ofNat]


/-- Comparisons, fall-through: recognition continues into the stores.  The
condition is `PrefixCalldata.branchCondition`, which
`branchCondition_eq_zero_iff` identifies with `PrefixBranch.Recognised`. -/
theorem run_compare_fall (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5372) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 3 < 1024)
    (hrec : PrefixBranch.Recognised input) :
    run comparePath s = some { s with pc := UInt256.ofNat 5450 } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hcond : PrefixCalldata.branchCondition
      (MachineState.readWord input 0) (MachineState.readWord input 32) = 0 :=
    (PrefixCalldata.branchCondition_eq_zero_iff input).2 hrec
  have w5372 : (UInt256.ofNat 5372).add (UInt256.ofNat 1) = UInt256.ofNat 5373 := by
    show UInt256.ofNat 5372 + UInt256.ofNat 1 = UInt256.ofNat 5373
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5373 : (UInt256.ofNat 5373).add (UInt256.ofNat 1) = UInt256.ofNat 5374 := by
    show UInt256.ofNat 5373 + UInt256.ofNat 1 = UInt256.ofNat 5374
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5374 : UInt256.ofNat 5374 + UInt256.ofNat 33 = UInt256.ofNat 5407 := by
    show UInt256.ofNat 5374 + UInt256.ofNat 33 = UInt256.ofNat 5407
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5407 : (UInt256.ofNat 5407).add (UInt256.ofNat 1) = UInt256.ofNat 5408 := by
    show UInt256.ofNat 5407 + UInt256.ofNat 1 = UInt256.ofNat 5408
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5408 : UInt256.ofNat 5408 + UInt256.ofNat 2 = UInt256.ofNat 5410 := by
    show UInt256.ofNat 5408 + UInt256.ofNat 2 = UInt256.ofNat 5410
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5410 : (UInt256.ofNat 5410).add (UInt256.ofNat 1) = UInt256.ofNat 5411 := by
    show UInt256.ofNat 5410 + UInt256.ofNat 1 = UInt256.ofNat 5411
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5411 : UInt256.ofNat 5411 + UInt256.ofNat 33 = UInt256.ofNat 5444 := by
    show UInt256.ofNat 5411 + UInt256.ofNat 33 = UInt256.ofNat 5444
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5444 : (UInt256.ofNat 5444).add (UInt256.ofNat 1) = UInt256.ofNat 5445 := by
    show UInt256.ofNat 5444 + UInt256.ofNat 1 = UInt256.ofNat 5445
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5445 : (UInt256.ofNat 5445).add (UInt256.ofNat 1) = UInt256.ofNat 5446 := by
    show UInt256.ofNat 5445 + UInt256.ofNat 1 = UInt256.ofNat 5446
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5446 : UInt256.ofNat 5446 + UInt256.ofNat 3 = UInt256.ofNat 5449 := by
    show UInt256.ofNat 5446 + UInt256.ofNat 3 = UInt256.ofNat 5449
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5449 : (UInt256.ofNat 5449).add (UInt256.ofNat 1) = UInt256.ofNat 5450 := by
    show UInt256.ofNat 5449 + UInt256.ofNat 1 = UInt256.ofNat 5450
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [comparePath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4581, pc4582, pc4583, pc4584, pc4585, pc4586, pc4587, pc4588, pc4589, pc4590, pc4591,
    hpc, hstack, hrun, hcalldata, PrefixCalldata.branchCondition, hcond,
    hlen, hc0, hc1, hc2,
    w5372, w5373, w5374, w5407, w5408, w5410, w5411, w5444, w5445, w5446, w5449]


/-- Comparisons, taken: a mismatch falls out to `5499`. -/
theorem run_compare_taken (s : State) (input : ByteArray) (rest : List UInt256)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5372) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 3 < 1024)
    (hrec : ¬ PrefixBranch.Recognised input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    run comparePath s = some { s with pc := UInt256.ofNat 5499 } := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hcond : PrefixCalldata.branchCondition
      (MachineState.readWord input 0) (MachineState.readWord input 32) ≠ 0 :=
    fun h => hrec ((PrefixCalldata.branchCondition_eq_zero_iff input).1 h)
  have hd5499 : Decode.isValidJumpDest Artifact.submissionArtifact.code 5499 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 4609 (by rfl)
  have w5372 : (UInt256.ofNat 5372).add (UInt256.ofNat 1) = UInt256.ofNat 5373 := by
    show UInt256.ofNat 5372 + UInt256.ofNat 1 = UInt256.ofNat 5373
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5373 : (UInt256.ofNat 5373).add (UInt256.ofNat 1) = UInt256.ofNat 5374 := by
    show UInt256.ofNat 5373 + UInt256.ofNat 1 = UInt256.ofNat 5374
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5374 : UInt256.ofNat 5374 + UInt256.ofNat 33 = UInt256.ofNat 5407 := by
    show UInt256.ofNat 5374 + UInt256.ofNat 33 = UInt256.ofNat 5407
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5407 : (UInt256.ofNat 5407).add (UInt256.ofNat 1) = UInt256.ofNat 5408 := by
    show UInt256.ofNat 5407 + UInt256.ofNat 1 = UInt256.ofNat 5408
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5408 : UInt256.ofNat 5408 + UInt256.ofNat 2 = UInt256.ofNat 5410 := by
    show UInt256.ofNat 5408 + UInt256.ofNat 2 = UInt256.ofNat 5410
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5410 : (UInt256.ofNat 5410).add (UInt256.ofNat 1) = UInt256.ofNat 5411 := by
    show UInt256.ofNat 5410 + UInt256.ofNat 1 = UInt256.ofNat 5411
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5411 : UInt256.ofNat 5411 + UInt256.ofNat 33 = UInt256.ofNat 5444 := by
    show UInt256.ofNat 5411 + UInt256.ofNat 33 = UInt256.ofNat 5444
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5444 : (UInt256.ofNat 5444).add (UInt256.ofNat 1) = UInt256.ofNat 5445 := by
    show UInt256.ofNat 5444 + UInt256.ofNat 1 = UInt256.ofNat 5445
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5445 : (UInt256.ofNat 5445).add (UInt256.ofNat 1) = UInt256.ofNat 5446 := by
    show UInt256.ofNat 5445 + UInt256.ofNat 1 = UInt256.ofNat 5446
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5446 : UInt256.ofNat 5446 + UInt256.ofNat 3 = UInt256.ofNat 5449 := by
    show UInt256.ofNat 5446 + UInt256.ofNat 3 = UInt256.ofNat 5449
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [comparePath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4581, pc4582, pc4583, pc4584, pc4585, pc4586, pc4587, pc4588, pc4589, pc4590, pc4591,
    hpc, hstack, hrun, hcalldata, PrefixCalldata.branchCondition, hcond,
    hlen, hc0, hc1, hc2,
    w5372, w5373, w5374, w5407, w5408, w5410, w5411, w5444, w5445, w5446,
    hcode, hd5499,
    Challenge.EvmProof.Word.literal_eq_ofNat]


/-- The five stores and the jump back to the driver loop head. -/
theorem run_store (s : State) (rest : List UInt256)
    (hpc : s.pc = UInt256.ofNat 5450) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 2 < 1024)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) :
    run storePath s = some (afterStores s) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hd466 : Decode.isValidJumpDest Artifact.submissionArtifact.code 466 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 263 (by rfl)
  have w5450 : UInt256.ofNat 5450 + UInt256.ofNat 5 = UInt256.ofNat 5455 := by
    show UInt256.ofNat 5450 + UInt256.ofNat 5 = UInt256.ofNat 5455
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5455 : UInt256.ofNat 5455 + UInt256.ofNat 3 = UInt256.ofNat 5458 := by
    show UInt256.ofNat 5455 + UInt256.ofNat 3 = UInt256.ofNat 5458
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5458 : (UInt256.ofNat 5458).add (UInt256.ofNat 1) = UInt256.ofNat 5459 := by
    show UInt256.ofNat 5458 + UInt256.ofNat 1 = UInt256.ofNat 5459
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5459 : UInt256.ofNat 5459 + UInt256.ofNat 5 = UInt256.ofNat 5464 := by
    show UInt256.ofNat 5459 + UInt256.ofNat 5 = UInt256.ofNat 5464
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5464 : UInt256.ofNat 5464 + UInt256.ofNat 3 = UInt256.ofNat 5467 := by
    show UInt256.ofNat 5464 + UInt256.ofNat 3 = UInt256.ofNat 5467
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5467 : (UInt256.ofNat 5467).add (UInt256.ofNat 1) = UInt256.ofNat 5468 := by
    show UInt256.ofNat 5467 + UInt256.ofNat 1 = UInt256.ofNat 5468
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5468 : UInt256.ofNat 5468 + UInt256.ofNat 5 = UInt256.ofNat 5473 := by
    show UInt256.ofNat 5468 + UInt256.ofNat 5 = UInt256.ofNat 5473
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5473 : UInt256.ofNat 5473 + UInt256.ofNat 3 = UInt256.ofNat 5476 := by
    show UInt256.ofNat 5473 + UInt256.ofNat 3 = UInt256.ofNat 5476
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5476 : (UInt256.ofNat 5476).add (UInt256.ofNat 1) = UInt256.ofNat 5477 := by
    show UInt256.ofNat 5476 + UInt256.ofNat 1 = UInt256.ofNat 5477
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5477 : UInt256.ofNat 5477 + UInt256.ofNat 5 = UInt256.ofNat 5482 := by
    show UInt256.ofNat 5477 + UInt256.ofNat 5 = UInt256.ofNat 5482
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5482 : UInt256.ofNat 5482 + UInt256.ofNat 3 = UInt256.ofNat 5485 := by
    show UInt256.ofNat 5482 + UInt256.ofNat 3 = UInt256.ofNat 5485
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5485 : (UInt256.ofNat 5485).add (UInt256.ofNat 1) = UInt256.ofNat 5486 := by
    show UInt256.ofNat 5485 + UInt256.ofNat 1 = UInt256.ofNat 5486
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5486 : UInt256.ofNat 5486 + UInt256.ofNat 5 = UInt256.ofNat 5491 := by
    show UInt256.ofNat 5486 + UInt256.ofNat 5 = UInt256.ofNat 5491
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5491 : UInt256.ofNat 5491 + UInt256.ofNat 3 = UInt256.ofNat 5494 := by
    show UInt256.ofNat 5491 + UInt256.ofNat 3 = UInt256.ofNat 5494
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5494 : (UInt256.ofNat 5494).add (UInt256.ofNat 1) = UInt256.ofNat 5495 := by
    show UInt256.ofNat 5494 + UInt256.ofNat 1 = UInt256.ofNat 5495
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  have w5495 : UInt256.ofNat 5495 + UInt256.ofNat 3 = UInt256.ofNat 5498 := by
    show UInt256.ofNat 5495 + UInt256.ofNat 3 = UInt256.ofNat 5498
    exact Challenge.EvmProof.Word.ofNat_add_ofNat (by norm_num)
  simp (config := { maxSteps := 400000 })
    [storePath, run, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    UInt256.succ, opAt, pushAt,
    pc4592, pc4593, pc4594, pc4595, pc4596, pc4597, pc4598, pc4599, pc4600, pc4601, pc4602, pc4603, pc4604, pc4605, pc4606, pc4607, pc4608,
    hpc, hstack, hrun, afterStores, storeActive5, storeActive, PrefixBranch.branchMemory,
    PackedCombineMemory.writeHash, PrefixBranch.loopHeadPC,
    hlen, hc0, hc1,
    w5450, w5455, w5458, w5459, w5464, w5467, w5468, w5473, w5476, w5477, w5482, w5485, w5486, w5491, w5494, w5495,
    hcode, hd466,
    Challenge.EvmProof.Word.literal_eq_ofNat]


/-! ## `GasSteps`

`sound`'s side conditions are auto-params that discharge by `rfl` only for
`stS`-shaped states, so on a generic running state they are passed explicitly. -/

/-- Recognition: entry at `5363` to the driver loop head with `H1` installed.
The intermediate states are named, because `.trans` must see the guard segment's
result as the comparison segment's entry. -/
def gasSteps_hit (s : State) (input : ByteArray) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5363) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 3 < 1024)
    (hsize : ¬ input.size < 64) (hrec : PrefixBranch.Recognised input) :
    GasSteps s (afterStores { s with pc := UInt256.ofNat 5450 }) :=
  (sound guardPath
      (run_guard_fall s input rest hcalldata hpc hstack hrun (by omega) hfit hsize)
      hcode hfork hrun hnp).trans
    ((sound comparePath
        (run_compare_fall { s with pc := UInt256.ofNat 5372 } input rest
          hcalldata rfl hstack hrun (by omega) hrec)
        hcode hfork hrun hnp).trans
      (sound storePath
        (run_store { s with pc := UInt256.ofNat 5450 } rest rfl hstack hrun (by omega) hcode)
        hcode hfork hrun hnp))

/-- Non-recognition: entry at `5363` to the original first-block body at `477`.
A short input is rejected by the size guard, a long mismatching one by the
comparisons; `¬ Recognised` is the single premise either way. -/
def gasSteps_miss (s : State) (input : ByteArray) (rest : List UInt256)
    (hfit : CalldataFits input)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hcalldata : s.executionEnv.calldata = input)
    (hpc : s.pc = UInt256.ofNat 5363) (hstack : s.stack = rest)
    (hrun : s.halt = .Running) (hlen : rest.length + 3 < 1024)
    (hmiss : ¬ PrefixBranch.Recognised input) :
    GasSteps s { s with pc := UInt256.ofNat PrefixBranch.originalBodyPC } := by
  by_cases hsz : input.size < 64
  · exact (sound guardPath
      (run_guard_taken s input rest hcalldata hpc hstack hrun (by omega) hsz hcode)
      hcode hfork hrun hnp).trans
      (sound fallbackPath
        (run_fallback { s with pc := UInt256.ofNat 5499 } rest rfl hstack hrun (by omega) hcode)
        hcode hfork hrun hnp)
  · exact (sound guardPath
      (run_guard_fall s input rest hcalldata hpc hstack hrun (by omega) hfit hsz)
      hcode hfork hrun hnp).trans
      ((sound comparePath
          (run_compare_taken { s with pc := UInt256.ofNat 5372 } input rest
            hcalldata rfl hstack hrun (by omega) hmiss hcode)
          hcode hfork hrun hnp).trans
        (sound fallbackPath
          (run_fallback { s with pc := UInt256.ofNat 5499 } rest rfl hstack hrun (by omega) hcode)
          hcode hfork hrun hnp))

#print axioms branchPath_instructions
#print axioms branchPath_indices

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranchSite

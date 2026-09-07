import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSwapLemmas
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-! Exact masked consume tail at instruction 2816, including its final JUMP. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskTailSite

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Ripemd160.Submission.Proofs.Bytecode

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

open private
  submissionInstructionsChunk0
  submissionInstructionsChunk1
  submissionInstructionsChunk2
  submissionInstructionsChunk3
  submissionInstructionsChunk4
  submissionInstructionsChunk5
  submissionInstructionsChunk6
  submissionInstructionsChunk7
  submissionInstructionsChunk8
  submissionInstructionsChunk9
  submissionInstructionsChunk10
  submissionInstructionsChunk11
  submissionInstructionsChunk12
  submissionInstructionsChunk13
  submissionInstructionsChunk14
  submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk0_length
  submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length
  submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length
  submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length
  submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length
  submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length
  submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length
  submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length
  submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def artifactPrefix : List Instr :=
  submissionInstructionsChunk0 ++
    submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++
    submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++
    submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++
    submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++
    submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++
    submissionInstructionsChunk11 ++
    submissionInstructionsChunk12 ++
    submissionInstructionsChunk13

private def tailBefore : List Instr :=
  artifactPrefix ++ submissionInstructionsChunk14.take 16

private def tailAfter : List Instr :=
  submissionInstructionsChunk14.drop 70 ++ submissionInstructionsChunk15 ++
    submissionInstructionsChunk16

private theorem tailBefore_length : tailBefore.length = 2816 := by
  simp [tailBefore, artifactPrefix]

private theorem artifactChunk14_tail :
    submissionInstructionsChunk14 =
      submissionInstructionsChunk14.take 16 ++
        CachedMaskTail.template ++ submissionInstructionsChunk14.drop 70 := by
  rfl

private theorem artifact_tail_split :
    Artifact.submissionArtifact.instructions =
      tailBefore ++ CachedMaskTail.template ++ tailAfter := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      artifactPrefix ++ submissionInstructionsChunk14 ++
        submissionInstructionsChunk15 ++ submissionInstructionsChunk16 := by
    simp only [Artifact.submissionInstructions, artifactPrefix, List.append_assoc]
  rw [hprefix]
  conv_lhs => rw [artifactChunk14_tail]
  simp only [tailBefore, tailAfter, List.append_assoc]

private theorem artifact_consume_split :
    Artifact.submissionArtifact.instructions =
      tailBefore ++ CachedMaskTail.template ++ tailAfter :=
  artifact_tail_split

private theorem tailInstructions_length : CachedMaskTail.template.length = 54 := by
  decide

private theorem tail_instruction_at (i : Nat)
    (hi : i < CachedMaskTail.template.length) :
    Artifact.submissionArtifact.instructions[2816 + i]? =
      CachedMaskTail.template[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    tailBefore CachedMaskTail.template
    tailAfter
    artifact_consume_split i hi
  simpa [tailBefore_length] using h

private theorem tail_instruction_pc (i : Nat)
    (hi : i ≤ CachedMaskTail.template.length) :
    Artifact.submissionArtifact.instructionPC (2816 + i) =
      0x101b + ArtifactByteLength.byteLength (CachedMaskTail.template.take i) := by
  have hzero := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    tailBefore CachedMaskTail.template
    tailAfter
    artifact_consume_split 0 (by omega)
  have hzero' : Artifact.submissionArtifact.instructionPC 2816 =
      (assembleBytes tailBefore).length := by
    simpa [tailBefore_length] using hzero
  have hbefore : (assembleBytes tailBefore).length = 0x101b :=
    hzero'.symm.trans QuadLayout.tail_pc
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    tailBefore CachedMaskTail.template
    tailAfter 2816 0x101b
    artifact_consume_split tailBefore_length hbefore i hi
  simpa only [ArtifactByteLength.byteLength_eq_assemble] using h

private theorem tail_instruction_pc_global (index : Nat)
    (hlo : 2816 ≤ index) (hhi : index ≤ 2870) :
    Artifact.submissionArtifact.instructionPC index =
      0x101b + ArtifactByteLength.byteLength
        (CachedMaskTail.template.take (index - 2816)) := by
  have hi : index - 2816 ≤ CachedMaskTail.template.length := by
    rw [tailInstructions_length]
    omega
  have h := tail_instruction_pc (index - 2816) hi
  simpa only [Nat.add_sub_of_le hlo] using h

private theorem tail_instruction_wellFormed (i : Nat)
    (hi : i < CachedMaskTail.template.length) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka
      ((CachedMaskTail.template)[i]'hi) := by
  exact StackRoundData.templateWellFormed_mem
    (instructions := CachedMaskTail.template) (by decide) _ (List.getElem_mem hi)

def tailLocated (i : Nat) (hi : i < CachedMaskTail.template.length) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka where
  index := 2816 + i
  instruction := ((CachedMaskTail.template)[i]'hi)
  atIndex := by
    simpa [List.getElem?_eq_getElem hi] using tail_instruction_at i hi
  wellFormed := tail_instruction_wellFormed i hi

def tailPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  (List.finRange CachedMaskTail.template.length).map
    (fun i => tailLocated i.val i.isLt)

theorem tailPath_length : tailPath.length = 54 := by
  simpa [tailPath] using tailInstructions_length

set_option linter.unusedSimpArgs false in
private theorem runLocatedBlock_tail_raw (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256) (rest : List UInt256)
    (hrun : s.halt = .Running) (hstack : rest.length < 1006)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath
        (CachedMaskTail.entry s left right ret rest) =
      StackRoundTrace.runInstrSeq CachedMaskTail.template
        (CachedMaskTail.entry s left right ret rest) := by
  have hcap0 : rest.length < 1024 := by omega
  have hcap1 : rest.length + 1 < 1024 := by omega
  have hcap2 : rest.length + 2 < 1024 := by omega
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have hcap8 : rest.length + 8 < 1024 := by omega
  have hcap9 : rest.length + 9 < 1024 := by omega
  have hcap10 : rest.length + 10 < 1024 := by omega
  have hcap11 : rest.length + 11 < 1024 := by omega
  have hcap12 : rest.length + 12 < 1024 := by omega
  have hcap13 : rest.length + 13 < 1024 := by omega
  have hcap14 : rest.length + 14 < 1024 := by omega
  have hcap15 : rest.length + 15 < 1024 := by omega
  have hcap16 : rest.length + 16 < 1024 := by omega
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [tailPath, List.finRange_succ, tailLocated,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, tail_instruction_pc_global,
      CachedMaskTail.template, QuadTailTemplate.quadTailBeforeJumpTemplate,
      QuadTailTemplate.c0Instructions, QuadTailTemplate.c1Instructions,
      QuadTailTemplate.c2Instructions, QuadTailTemplate.c3Instructions,
      QuadTailTemplate.c4Instructions, QuadTailTemplate.storeH0Instructions,
      QuadTailTemplate.cleanupInstructions, QuadTailTemplate.swap5H,
      QuadTailTemplate.swap6H, QuadTailTemplate.swap7H,
      StackRoundTemplate.op, StackRoundTemplate.push1, StackRoundTemplate.push4,
      StackRoundTemplate.swap1, StackRoundTemplate.swap2, StackRoundTemplate.swap3,
      CachedMaskTail.entry, QuadTailTemplate.workingStack, StackRoundTemplate.mask,
      QuadTailTemplate.tailStartPC, QuadTailTemplate.factor,
      StackRoundTrace.runInstrSeq, Challenge.EvmProof.Stepper.runInstr, hrun, hvalid,
      hcap0, hcap1, hcap2, hcap3, hcap4, hcap5, hcap6, hcap7, hcap8, hcap9, hcap10, hcap11, hcap12, hcap13, hcap14, hcap15, hcap16,
      QuadSwapLemmas.exchange_swap1, QuadSwapLemmas.exchange_swap2,
      QuadSwapLemmas.exchange_swap3, QuadSwapLemmas.exchange_swap5,
      QuadSwapLemmas.exchange_swap6, QuadSwapLemmas.exchange_swap7,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.add_assoc, List.getElem?_cons_zero, List.getElem?_cons_succ,
      ArtifactByteLength.byteLength]

theorem runLocatedBlock_tail (s : State)
    (left right : Compression.EvmWorking) (ret : UInt256) (rest : List UInt256)
    (hactive : 25 ≤ s.activeWords.toNat) (hstack : rest.length < 1006)
    (hrun : s.halt = .Running) (hfork : s.fork = .Osaka)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath
        (CachedMaskTail.entry s left right ret rest) =
      some (QuadTailTemplate.finalResult s left right ret rest) := by
  rw [runLocatedBlock_tail_raw s left right ret rest hrun hstack hvalid]
  exact CachedMaskTail.run s left right ret rest hrun hfork hactive hstack hvalid

def actualTailGasSteps (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256)
    (hactive : 25 ≤ s.activeWords.toNat) (hstack : rest.length < 1006)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    GasSteps (CachedMaskTail.entry s left right ret rest)
      (QuadTailTemplate.finalResult s left right ret rest) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tailPath
  · simpa [CachedMaskTail.entry] using hcode
  · simpa [CachedMaskTail.entry] using hfork
  · exact runLocatedBlock_tail s left right ret rest hactive hstack hrun hfork hvalid
  · simpa [CachedMaskTail.entry] using hrun
  · simpa [CachedMaskTail.entry] using hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskTailSite

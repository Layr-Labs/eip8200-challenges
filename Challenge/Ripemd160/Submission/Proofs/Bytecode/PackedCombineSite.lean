import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEndpoint
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000

/-!
# Exact final-artifact sites for the packed combine

The artifact lookup is split at the dynamic `JUMP`: indices `4401 .. 4478`
form a contiguous straight-line body from PC 5066 to PC 5169, and index 4479
is the return jump itself.  The next artifact instruction is the output-path
`JUMPDEST` at PC 5170; it is not part of this trace.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineSite

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open StackRoundTemplate
open PackedCombineTrace

private theorem code_bound :
    Artifact.submissionArtifact.code.size < UInt256.size := by
  exact StackRoundData.artifact_code_bound

private theorem body_slice :
    (Artifact.submissionArtifact.instructions.drop 4401).take
      combineBody.length = combineBody := by
  rfl

/-- Exact straight-line combine body in the final artifact. -/
def bodySite : GenericRoundSite Artifact.submissionArtifact .Osaka combineBody :=
  StackSiteBuilder.ofSlice combineBody 4401 body_slice
    (by
      change 4401 + combineBody.length ≤ Artifact.submissionInstructions.length
      rw [combineBody_length, Artifact.referenceInstructions_count]
      decide)
    code_bound
    (StackRoundData.templateWellFormed_mem (instructions := combineBody) (by decide))
    (by decide)

@[simp] theorem bodySite_startPC :
    bodySite.startPC = UInt256.ofNat 5066 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4401) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] theorem bodySite_endPC :
    bodySite.endPC = UInt256.ofNat 5169 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4479) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt
    (Artifact.submissionArtifact.instructionPC_le_code_size index) code_bound

/-- The dynamic return `JUMP` at exact instruction index 4479 / PC 5169. -/
def jumpSite : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 4479
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4479)
  pc_eq := pc_toNat_instructionPC 4479

def jumpPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [jumpSite.located]

@[simp] theorem jumpSite_pc : jumpSite.pc = UInt256.ofNat 5169 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4479) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem bodySite_end_eq_jumpSite : bodySite.endPC = jumpSite.pc := by
  rw [bodySite_endPC, jumpSite_pc]

/-- The actual driver return target is instruction index 263 / byte PC 466. -/
theorem return466_isValidJumpDest :
    Decode.isValidJumpDest Artifact.submissionArtifact.code 466 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 263 = 466 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 263 (by rfl)
  rwa [hpc] at h

private def sitePush1 (value : Nat) : Instr :=
  .push ⟨1, by decide⟩ (UInt256.ofNat value)

private def sitePush2 (value : Nat) : Instr :=
  .push ⟨2, by decide⟩ (UInt256.ofNat value)

private def siteDup (index : Fin 16) : Instr := .op (.Dup ⟨index⟩)

private def siteCombine0 : List Instr :=
  [sitePush2 352, .op .MLOAD, siteDup 3, siteDup 5, sitePush1 64, .op .SHR,
   .op .ADD, sitePush2 384, .op .MLOAD, .op .ADD, siteDup 8, .op .AND,
   sitePush2 352, .op .MSTORE]

private def siteCombine1 : List Instr :=
  [siteDup 4, siteDup 6, sitePush1 64, .op .SHR, .op .ADD, sitePush2 416,
   .op .MLOAD, .op .ADD, siteDup 8, .op .AND, sitePush2 384, .op .MSTORE]

private def siteCombine2 : List Instr :=
  [siteDup 5, siteDup 2, sitePush1 64, .op .SHR, .op .ADD, sitePush2 448,
   .op .MLOAD, .op .ADD, siteDup 8, .op .AND, sitePush2 416, .op .MSTORE]

private def siteCombine3 : List Instr :=
  [siteDup 1, siteDup 3, sitePush1 64, .op .SHR, .op .ADD, sitePush2 480,
   .op .MLOAD, .op .ADD, siteDup 8, .op .AND, sitePush2 448, .op .MSTORE]

private def siteCombine4 : List Instr :=
  [siteDup 2, siteDup 4, sitePush1 64, .op .SHR, .op .ADD, siteDup 1,
   .op .ADD, siteDup 8, .op .AND, sitePush2 480, .op .MSTORE]

private def siteCleanup : List Instr :=
  [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP,
   .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

private theorem combineBody_eq_siteStages :
    combineBody =
      siteCombine0 ++ siteCombine1 ++ siteCombine2 ++ siteCombine3 ++
        siteCombine4 ++ siteCleanup := by
  rfl

private theorem advances_straight {instruction : Instr}
    (h : StraightLine instruction) : DenseScheduleLift.Advances instruction := by
  exact Or.inl (Or.inl h)

private theorem advances_mstore :
    DenseScheduleLift.Advances (.op .MSTORE) := by
  exact Or.inr (Or.inl rfl)

private theorem advances_append {first second : List Instr}
    (hfirst : ∀ instruction ∈ first, DenseScheduleLift.Advances instruction)
    (hsecond : ∀ instruction ∈ second, DenseScheduleLift.Advances instruction) :
    ∀ instruction ∈ first ++ second, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [List.mem_append] at hmem
  rcases hmem with hmem | hmem
  · exact hfirst instruction hmem
  · exact hsecond instruction hmem

private theorem siteCombine0_advances :
    ∀ instruction ∈ siteCombine0, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCombine0, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact advances_mstore
    | exact advances_straight (by constructor)

private theorem siteCombine1_advances :
    ∀ instruction ∈ siteCombine1, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCombine1, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact advances_mstore
    | exact advances_straight (by constructor)

private theorem siteCombine2_advances :
    ∀ instruction ∈ siteCombine2, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCombine2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact advances_mstore
    | exact advances_straight (by constructor)

private theorem siteCombine3_advances :
    ∀ instruction ∈ siteCombine3, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCombine3, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals first
    | exact advances_mstore
    | exact advances_straight (by constructor)

private theorem siteCombine4_advances :
    ∀ instruction ∈ siteCombine4, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCombine4, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals first
    | exact advances_mstore
    | exact advances_straight (by constructor)

private theorem siteCleanup_advances :
    ∀ instruction ∈ siteCleanup, DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [siteCleanup, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem body_advances :
    ∀ instruction ∈ combineBody, DenseScheduleLift.Advances instruction := by
  rw [combineBody_eq_siteStages]
  apply advances_append
  · apply advances_append
    · apply advances_append
      · apply advances_append
        · apply advances_append
          · exact siteCombine0_advances
          · exact siteCombine1_advances
        · exact siteCombine2_advances
      · exact siteCombine3_advances
    · exact siteCombine4_advances
  · exact siteCleanup_advances

private theorem runLocatedBlock_singleton
    {artifact : ProgramArtifact} {fork : Fork}
    (located : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [located] s =
      Challenge.EvmProof.Stepper.runLocated located s := by
  cases h : Challenge.EvmProof.Stepper.runLocated located s with
  | none => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]
  | some t => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]

theorem runLocatedBlock_body (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock bodySite.path
        (entryState s g ret xoff xend rest) =
      some (preJumpState s g ret xoff xend rest) := by
  rw [DenseScheduleLift.runLocatedBlock_eq_raw bodySite body_advances]
  · exact run_combineBody s g ret xoff xend rest hactive hstack hrun
  · simp [entryState]

private theorem runInstr_jump (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1001)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runInstr (.op .JUMP) (preJumpState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
  have hraw := run_returnJump s g ret xoff xend rest hstack hvalid
  change (match Stepper.runInstr (.op .JUMP)
      (preJumpState s g ret xoff xend rest) with
    | none => none
    | some next => some next) = some (resultState s g ret xoff xend rest) at hraw
  cases h : Stepper.runInstr (.op .JUMP)
      (preJumpState s g ret xoff xend rest) with
  | none => simp [h] at hraw
  | some next =>
      simpa [h] using hraw

theorem runLocatedBlock_jump (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1001)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runLocatedBlock jumpPath (preJumpState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
  have hpc : (preJumpState s g ret xoff xend rest).pc.toNat =
      Artifact.submissionArtifact.instructionPC jumpSite.located.index := by
    calc
      (preJumpState s g ret xoff xend rest).pc.toNat = jumpSite.pc.toNat := by
        rw [jumpSite_pc]
        simp [preJumpState]
      _ = Artifact.submissionArtifact.instructionPC jumpSite.located.index :=
        jumpSite.pc_eq
  have hlocated : Stepper.runLocated jumpSite.located
      (preJumpState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
    simpa [Stepper.runLocated, jumpSite, hpc] using
      runInstr_jump s g ret xoff xend rest hstack hvalid
  change Stepper.runLocatedBlock [jumpSite.located] _ = _
  rw [runLocatedBlock_singleton]
  exact hlocated

def combinePath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  bodySite.path ++ jumpPath

theorem runLocatedBlock_combineTail (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    Stepper.runLocatedBlock combinePath (entryState s g ret xoff xend rest) =
      some (resultState s g ret xoff xend rest) := by
  apply Stepper.runLocatedBlock_append bodySite.path jumpPath
    (entryState s g ret xoff xend rest)
    (preJumpState s g ret xoff xend rest)
    (resultState s g ret xoff xend rest)
  · exact runLocatedBlock_body s g ret xoff xend rest hactive hstack hrun
  · simpa [preJumpState] using hrun
  · exact runLocatedBlock_jump s g ret xoff xend rest hstack hvalid

def gasSteps_combineTail (s : State) (g : PackedStepCorrected.Regs)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    GasSteps (entryState s g ret xoff xend rest)
      (resultState s g ret xoff xend rest) := by
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka combinePath
  · simpa [entryState] using hcode
  · simpa [entryState, State.fork] using hfork
  · exact runLocatedBlock_combineTail s g ret xoff xend rest
      hactive hstack hrun hvalid
  · simpa [entryState] using hrun
  · simpa [entryState] using hnp

/-- Exact actual-driver specialization: the return word is PC 466. -/
def gasSteps_combineTail_return466 (s : State) (g : PackedStepCorrected.Regs)
    (xoff xend : UInt256) (rest : List UInt256)
    (hactive : 16 ≤ s.activeWords.toNat)
    (hstack : rest.length < 1001)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entryState s g (UInt256.ofNat 466) xoff xend rest)
      (resultState s g (UInt256.ofNat 466) xoff xend rest) := by
  apply gasSteps_combineTail s g (UInt256.ofNat 466) xoff xend rest
    hactive hstack hcode hfork hrun hnp
  rw [hcode, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (466 : Nat) < 2 ^ 256)]
  exact return466_isValidJumpDest

/-- The full-round endpoint supplies exactly the stack consumed by this
trace.  This is a shape bridge only; the body theorem separately supplies the
GasSteps witness to PC 5066. -/
theorem entryStack_endpoint (memory : ByteArray) (words : Nat → UInt256)
    (h : Compression.HashState) (ret xoff xend : UInt256)
    (rest : List UInt256) :
    entryStack (PackedCompressionEndpoint.endpoint memory words h ret xoff xend).regs
        ret xoff xend rest =
      PackedStepFrame.frameStack
          (PackedCompressionEndpoint.endpoint memory words h ret xoff xend) ++ rest := by
  rw [PackedCompressionEndpoint.endpoint_stack]
  rfl

#print axioms return466_isValidJumpDest
#print axioms runLocatedBlock_combineTail
#print axioms gasSteps_combineTail_return466
#print axioms entryStack_endpoint

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineSite

import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowDispatchCore
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatNext

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.Paths
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-! ## Artifact-agnostic readings of a certified slice

`WindowTwentyOneSlice.locations` reads its slice as `artifact.instructions[start + k]` for
each `k`; on a 4,360-instruction list that is `O(start)` work per instruction, and the two
`rfl` obligations of `block` pay it twice (elaborator and kernel).  The two lemmas below are
proved for an ARBITRARY `artifact : ProgramArtifact`, so no concrete bytecode enters them;
the concrete submission is then touched once per obligation, and its instruction prefix is
assembled exactly once, at `pcAnchorBlocks`.  Every `Block` statement is unchanged. -/

open Challenge.EvmProof Challenge.EvmProof.Stepper in
/-- A certified consecutive slice reads as one `drop`/`take` of the instruction list. -/
private theorem locations_map_instruction {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start count : Nat)
    (hbound : start + count ≤ artifact.instructions.length) :
    (WindowTwentyOneSlice.locations cert start count hbound).map Located.instruction =
      (artifact.instructions.drop start).take count := by
  induction count generalizing start with
  | zero => simp [WindowTwentyOneSlice.locations]
  | succ count ih =>
      have hlt : start < artifact.instructions.length := by omega
      rw [WindowTwentyOneSlice.locations, List.map_cons, ih (start + 1) (by omega),
        List.drop_eq_getElem_cons hlt, List.take_succ_cons]
      rfl

/-- `instructionPC` advances by the assembled length of the intervening slice. -/
private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private def nine_base :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 717 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 503 1 717 WindowTwentyOneEntry.baseProgram
    (by change 503 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 718 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 504 2 718 WindowTwentyOneEntry.modulusProgram
    (by change 504 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 720 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 506 88 720 WindowTwentyOneTableBuild.program
    (by change 506 + 88 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 809 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 594 3 809 WindowPrecopyRoute.setupProgram
    (by change 594 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 813 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 597 7 813 WindowPrecopyRoute.copyProgram
    (by change 597 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 821 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 604 314 821 WindowPrecopyRoute.poolProgram
    (by change 604 + 314 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1135 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 918 5 1135 WindowPrecopyRoute.firstProgram
    (by change 918 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1144 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 923 840 1144 (WindowPrecopyRoute.routeWindows 0 60)
    (by change 923 + 840 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 2224 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1763 49 2224 WindowPrecopyRoute.tailProgram
    (by change 1763 + 49 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 16 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 9 6 16 FermatNext.fastProgram
    (by change 9 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_merge :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 25 FermatNext.mergeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 15 10 25 FermatNext.mergeProgram
    (by change 15 + 10 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_recheck :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 40 FermatNext.recheckProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 25 6 40 FermatNext.recheckProgram
    (by change 25 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10741 FermatNext.joinProgram where
  path := [CycleSubmission.Global.Fast.opAt 8401 .JUMPDEST,
   CycleSubmission.Global.Fast.opAt 8402 (.Dup ⟨1,by decide⟩),
   CycleSubmission.Global.Fast.opAt 8403 .NOT,
   CycleSubmission.Global.Fast.opAt 8404 (.Dup ⟨1,by decide⟩),
   CycleSubmission.Global.Fast.opAt 8405 .ADD,
   CycleSubmission.Global.Fast.pushAt 8406 2 717,
   CycleSubmission.Global.Fast.opAt 8407 .JUMPI]
  instructions_eq := by rfl
  layout := by
    have hp0 : CycleSubmission.Artifact.artifact.instructionPC 8401 = 10741 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp1 : CycleSubmission.Artifact.artifact.instructionPC 8402 = 10742 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp2 : CycleSubmission.Artifact.artifact.instructionPC 8403 = 10743 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp3 : CycleSubmission.Artifact.artifact.instructionPC 8404 = 10744 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp4 : CycleSubmission.Artifact.artifact.instructionPC 8405 = 10745 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp5 : CycleSubmission.Artifact.artifact.instructionPC 8406 = 10746 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp6 : CycleSubmission.Artifact.artifact.instructionPC 8407 = 10749 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    simp [Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated.LinearPath,
      Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated.Linear,
      CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt,
      hp0, hp1, hp2, hp3, hp4, hp5, hp6,
      Challenge.EvmProof.Word.ofNat_add_mod]

private def fermat_toPrime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10750 FermatNext.toPrimeProgram where
  path := [CycleSubmission.Global.Fast.pushAt 8408 2 10471,
   CycleSubmission.Global.Fast.opAt 8409 .JUMP]
  instructions_eq := by rfl
  layout := by
    have hp0 : CycleSubmission.Artifact.artifact.instructionPC 8408 = 10750 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    have hp1 : CycleSubmission.Artifact.artifact.instructionPC 8409 = 10753 := by
      rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
    simp [Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated.LinearPath,
      Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated.Linear,
      CycleSubmission.Global.Fast.opAt, CycleSubmission.Global.Fast.pushAt,
      hp0, hp1,
      Challenge.EvmProof.Word.ofNat_add_mod]

private def fermat_prime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10471 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8205 11 10471 FermatNext.primeProgram
    (by change 8205 + 11 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_jumpTail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10521 FermatNext.jumpTailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8216 2 10521 FermatNext.jumpTailProgram
    (by change 8216 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4627 FermatNext.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3612 1 4627 FermatNext.tailProgram
    (by change 3612 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4628 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3613 9 4628 FermatProgram.returnProgram
    (by change 3613 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 96 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 43 9 96 FermatNext.genCheckProgram
    (by change 43 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 107 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 52 18 107 FermatNext.genLoadProgram
    (by change 52 + 18 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_fastJoin :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 48 FermatNext.fastJoinProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 31 6 48 FermatNext.fastJoinProgram
    (by change 31 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_fastToPrime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 56 FermatNext.toPrimeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 37 2 56 FermatNext.toPrimeProgram
    (by change 37 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def fermatPaths : FermatNext.Paths CycleSubmission.Artifact.artifact .Osaka where
  fast := fermat_fast
  merge := fermat_merge
  recheck := fermat_recheck
  fastJoin := fermat_fastJoin
  fastToPrime := fermat_fastToPrime
  join := fermat_join
  toPrime := fermat_toPrime
  prime := fermat_prime
  jumpTail := fermat_jumpTail
  tail := fermat_tail
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact CycleSubmission.Global.Binding.jumpDest 503 (by rfl)
  joinJump := CycleSubmission.Global.Binding.jumpDest 8401 (by rfl)
  tailJump := by exact CycleSubmission.Global.Binding.jumpDest 3612 (by rfl)
  bigJump := by exact CycleSubmission.Global.Binding.jumpDest 134 (by rfl)
  primeJump := by exact CycleSubmission.Global.Binding.jumpDest 8205 (by rfl)
  genJump := by exact CycleSubmission.Global.Binding.jumpDest 43 (by rfl)

def twentyOnePaths : WindowDispatchCore.Paths CycleSubmission.Artifact.artifact .Osaka where
  base := nine_base
  modulus := nine_modulus
  table := nine_table
  setup := nine_setup
  copy := nine_copy
  pool := nine_pool
  first := nine_first
  head := nine_head
  tail := nine_tail
end CycleSubmission.Global.Paths

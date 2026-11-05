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
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 745 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 512 1 745 WindowTwentyOneEntry.baseProgram
    (by change 512 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 746 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 513 2 746 WindowTwentyOneEntry.modulusProgram
    (by change 513 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 748 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 515 88 748 WindowTwentyOneTableBuild.program
    (by change 515 + 88 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 837 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 603 3 837 WindowPrecopyRoute.setupProgram
    (by change 603 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 841 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 606 7 841 WindowPrecopyRoute.copyProgram
    (by change 606 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 849 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 613 314 849 WindowPrecopyRoute.poolProgram
    (by change 613 + 314 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1163 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 927 5 1163 WindowPrecopyRoute.firstProgram
    (by change 927 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1172 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 932 840 1172 (WindowPrecopyRoute.routeWindows 0 60)
    (by change 932 + 840 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 2252 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1772 49 2252 WindowPrecopyRoute.tailProgram
    (by change 1772 + 49 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
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
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 48 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 31 7 48 FermatNext.joinProgram
    (by change 31 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_toPrime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 57 FermatNext.toPrimeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 38 2 57 FermatNext.toPrimeProgram
    (by change 38 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10698 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8322 11 10698 FermatNext.primeProgram
    (by change 8322 + 11 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_jumpTail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 10748 FermatNext.jumpTailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8333 2 10748 FermatNext.jumpTailProgram
    (by change 8333 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4847 FermatNext.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3700 1 4847 FermatNext.tailProgram
    (by change 3700 + 1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4848 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3701 9 4848 FermatProgram.returnProgram
    (by change 3701 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 101 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 46 9 101 FermatNext.genCheckProgram
    (by change 46 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 112 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 55 18 112 FermatNext.genLoadProgram
    (by change 55 + 18 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

def fermatPaths : FermatNext.Paths CycleSubmission.Artifact.artifact .Osaka where
  fast := fermat_fast
  merge := fermat_merge
  recheck := fermat_recheck
  join := fermat_join
  toPrime := fermat_toPrime
  prime := fermat_prime
  jumpTail := fermat_jumpTail
  tail := fermat_tail
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact CycleSubmission.Global.Binding.jumpDest 512 (by rfl)
  joinJump := by exact CycleSubmission.Global.Binding.jumpDest 31 (by rfl)
  tailJump := by exact CycleSubmission.Global.Binding.jumpDest 3700 (by rfl)
  bigJump := by exact CycleSubmission.Global.Binding.jumpDest 143 (by rfl)
  primeJump := by exact CycleSubmission.Global.Binding.jumpDest 8322 (by rfl)
  genJump := by exact CycleSubmission.Global.Binding.jumpDest 46 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths CycleSubmission.Artifact.artifact .Osaka where
  base := nine_base
  modulus := nine_modulus
  table := nine_table
  setup := nine_setup
  copy := nine_copy
  pool := nine_pool
  first := nine_first
  head := nine_head
  tail := nine_tail
  genJump := by
    have h := CycleSubmission.Global.Binding.jumpDest 46 (by rfl)
    exact h
  missJump := by
    have h := CycleSubmission.Global.Binding.jumpDest 74 (by rfl)
    exact h

end CycleSubmission.Global.Paths

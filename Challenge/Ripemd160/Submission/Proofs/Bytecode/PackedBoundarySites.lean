import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSites

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Exact constant-swap sites between packed round groups

The 80 round sites are separated by four three-instruction constant swaps.
This module binds those twelve instructions to the final artifact and lifts
each swap to a gas-parametric EVM trace.  It supplies the boundary pieces for
per-round composition; it does not combine the whole compression into one
coarse-cap located plan.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate

/-- Instruction index of the swap after groups zero through three. -/
def boundaryStartIndex (boundary : Fin 4) : Nat :=
  match boundary.val with
  | 0 => 1253
  | 1 => 2104
  | 2 => 2795
  | _ => 3646

/-- The first three packed constants need twelve bytes; the final right-line
zero constant leaves only the four-byte left-line constant. -/
def boundaryPushWidth (boundary : Fin 4) : Fin 33 :=
  if boundary.val = 3 then ⟨4, by decide⟩ else ⟨12, by decide⟩

def boundaryTemplate (boundary : Fin 4) : List Instr :=
  [.push (boundaryPushWidth boundary) (packedK (boundary.val + 1)),
   .op (.Swap ⟨15, by decide⟩),
   .op .POP]

theorem boundary_encoding (boundary : Fin 4) :
    EncodesSequence (kSwap (boundary.val + 1)) (boundaryTemplate boundary) := by
  unfold kSwap boundaryTemplate
  exact EncodesSequence.cons
    (EncodesShape.push (boundaryPushWidth boundary) (packedK (boundary.val + 1))
      (by fin_cases boundary <;> decide))
    (EncodesSequence.cons (EncodesShape.swap (15 : Fin 16))
      (EncodesSequence.cons EncodesShape.pop EncodesSequence.nil))

private theorem boundary_slice (boundary : Fin 4) :
    (Artifact.submissionArtifact.instructions.drop
      (boundaryStartIndex boundary)).take (boundaryTemplate boundary).length =
        boundaryTemplate boundary := by
  fin_cases boundary <;> rfl

private theorem boundary_fits (boundary : Fin 4) :
    boundaryStartIndex boundary + (boundaryTemplate boundary).length ≤
      Artifact.submissionArtifact.instructions.length := by
  change boundaryStartIndex boundary + (boundaryTemplate boundary).length ≤
    Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  fin_cases boundary <;> decide

private theorem boundary_wellFormed (boundary : Fin 4) :
    ∀ instruction ∈ boundaryTemplate boundary,
      Stepper.WellFormed .Osaka instruction := by
  exact StackRoundData.templateWellFormed_mem (by
    fin_cases boundary <;> decide)

private theorem boundary_nonempty (boundary : Fin 4) :
    boundaryTemplate boundary ≠ [] := by
  fin_cases boundary <;> decide

def boundarySite (boundary : Fin 4) :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      (boundaryTemplate boundary) :=
  StackSiteBuilder.ofSlice (boundaryTemplate boundary)
    (boundaryStartIndex boundary) (boundary_slice boundary)
    (boundary_fits boundary) StackRoundData.artifact_code_bound
    (boundary_wellFormed boundary) (boundary_nonempty boundary)

theorem boundary_straightLine (boundary : Fin 4) :
    StraightLineLocated (kSwap (boundary.val + 1))
      (boundarySite boundary).path := by
  exact straightLineLocated_of_genericRoundSite (boundarySite boundary)
    (boundary_encoding boundary)

/-- Generic stack effect factored before the table-derived packed constant is
introduced.  This is the proved `PackedBoundarySwap.swap_exec` argument: it
avoids reducing `packedK` throughout the symbolic frame simplification. -/
theorem swap_exec (memAt : UInt256 → UInt256) (constant : UInt256)
    (frame : PackedStepFrame.Frame) (rest : List UInt256) :
    runOps memAt [Op.push constant, Op.swap 16, Op.pop]
      (frameStack frame ++ rest) =
        some (frameStack (replaceK constant frame) ++ rest) := by
  obtain ⟨regs, suffix, phase⟩ := frame
  cases phase <;>
    simp only [frameStack, regsStack, suffixStack, replaceK, runOps, runOp,
      List.cons_append, List.nil_append, List.getElem?_cons_succ,
      List.getElem?_cons_zero, List.set_cons_succ, List.set_cons_zero,
      Option.map_some, Option.bind_some, Nat.reduceSub]

/-- Abstract stack effect of one group-boundary constant replacement. -/
theorem kSwap_exec (memAt : UInt256 → UInt256) (group : Nat)
    (frame : PackedStepFrame.Frame) (rest : List UInt256) :
    runOps memAt (kSwap group) (frameStack frame ++ rest) =
      some (frameStack (replaceK (packedK group) frame) ++ rest) :=
  swap_exec memAt (packedK group) frame rest

/-- Actual gas-parametric EVM certificate for one of the four boundary swaps.
The caller supplies only the boundary-entry state facts and the small local
stack budget; the exact located path comes from `boundarySite`. -/
theorem boundary_certificate (boundary : Fin 4) (s : State)
    (frame : PackedStepFrame.Frame) (rest : List UInt256)
    (hstack : s.stack = frameStack frame ++ rest)
    (hbudget : s.stack.length + (kSwap (boundary.val + 1)).length < 1024)
    (hstart : PathStarts (boundarySite boundary).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, Stepper.runLocatedBlock (boundarySite boundary).path s = some t ∧
      ∃ _trace : GasSteps s t,
        t.stack = frameStack
          (replaceK (packedK (boundary.val + 1)) frame) ++ rest ∧
        t.memory = s.memory := by
  apply roundsCertificate (boundary_straightLine boundary) hbudget hstart
    hcode hfork hrun hnp
  rw [hstack]
  exact kSwap_exec (memoryWord s) (boundary.val + 1) frame rest

#print axioms boundary_straightLine
#print axioms boundary_certificate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySites

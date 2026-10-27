import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExitLift
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Join markers and hops

The specialised pad-only prefix lives in two padding windows and rejoins the
generic compressor at the marker inserted before round 13.  A marker is a lone
`JUMPDEST`; a hop is `PUSH2 target; JUMP`.  Both leave the stack unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Jumpdest
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def markTemplate : List Instr := [.op .JUMPDEST]

theorem run_mark (s : State) (pc : UInt256) (st : List UInt256)
    (hstack : st.length ≤ 1000) (hrun : s.halt = .Running) :
    runInstrSeq markTemplate {s with pc := pc, stack := st} =
      some {s with pc := pcAfter pc markTemplate, stack := st} := by
  have hbase : st.length < 1024 := by omega
  simp (discharger := omega) [markTemplate, runInstrSeq, DataStepper.runInstr, pcAfter,
    UInt256.succ, Instr.size, hrun, hbase, Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  rfl

/-- A marker at artifact instruction `index`, byte `pc`. -/
def markSite (index : Nat) (h : (HoistedInherited.Artifact.submissionArtifact.instructions.drop index).take markTemplate.length = markTemplate)
    (hb : index + markTemplate.length ≤ HoistedInherited.Artifact.submissionInstructions.length) :
    GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka markTemplate :=
  StackSiteBuilder.ofSlice markTemplate index h hb
    HoistedInherited.StackRoundData.artifact_code_bound
    (HoistedInherited.StackRoundData.templateWellFormed_mem (instructions := markTemplate) (by decide))
    (by decide)

theorem mark_advances : ∀ instruction ∈ markTemplate, DenseScheduleLift.Advances instruction := by
  apply HoistedInherited.Table80SiteCommon.coreAdvancesAll_sound
  decide

/-- The marker inserted before generic round 13 (instruction 946, byte 1557). -/
theorem core_slice :
    (HoistedInherited.Artifact.submissionArtifact.instructions.drop 946).take markTemplate.length = markTemplate := by rfl

def coreSite : GenericRoundSite HoistedInherited.Artifact.submissionArtifact .Osaka markTemplate :=
  markSite 946 core_slice
    (by rw [HoistedInherited.Artifact.referenceInstructions_count]; decide)

theorem core_pc : coreSite.startPC = UInt256.ofNat 1557 := by
  change UInt256.ofNat (HoistedInherited.Artifact.submissionArtifact.instructionPC 946) = UInt256.ofNat 1557
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_core (s : State) (st : List UInt256) (hstack : st.length ≤ 1000)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1557, stack := st}
      {s with pc := UInt256.ofNat 1558, stack := st} := by
  have hraw := run_mark s (UInt256.ofNat 1557) st hstack hrun
  have hend : pcAfter (UInt256.ofNat 1557) markTemplate = UInt256.ofNat 1558 := by decide
  rw [hend] at hraw
  exact DenseScheduleLift.gasSteps_of_raw coreSite _ _ hcode hfork hrun hnp core_pc.symm mark_advances hraw

theorem valid_core (s : State) (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 1557).toNat = true := by
  have hpc : HoistedInherited.Artifact.submissionArtifact.instructionPC 946 = 1557 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 946 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 1557 = true
  rw [hcode]
  exact h

/-! ## Hops -/

def hopTemplate (target : Nat) : List Instr :=
  [.push ⟨2, by decide⟩ (UInt256.ofNat target), .op .JUMP]

theorem run_hop (s : State) (pc : UInt256) (target : Nat) (st : List UInt256)
    (hstack : st.length ≤ 1000) (hrun : s.halt = .Running) (htarget : target < 2 ^ 16)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code target = true) :
    runInstrSeq (hopTemplate target) {s with pc := pc, stack := st} =
      some {s with pc := UInt256.ofNat target, stack := st} := by
  have hb0 : st.length < 1024 := by omega
  have hb1 : st.length + 1 < 1024 := by omega
  have ht : (UInt256.ofNat target).toNat = target := by
    rw [Word.word_toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp (discharger := omega) [hopTemplate, runInstrSeq, DataStepper.runInstr, hrun, hb0, hb1, ht, hvalid,
    List.length_cons, List.exchange, List.getElem?_cons_zero, pcAfter,
    UInt256.succ, Instr.size, Nat.add_assoc, Word.literal_eq_ofNat]

#print axioms gasSteps_core
#print axioms run_hop
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Jumpdest

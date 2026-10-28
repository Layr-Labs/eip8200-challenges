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

A marker is a lone `JUMPDEST`; a hop is `PUSH2 target; JUMP`.  Both leave the
stack unchanged.
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

#print axioms run_hop
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Jumpdest

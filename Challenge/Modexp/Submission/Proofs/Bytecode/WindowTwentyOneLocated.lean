import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper WindowNibbleKernel

/-- A successful instruction in this class advances linearly and preserves halt.
Unsupported instructions still cannot produce a successful symbolic run. -/
def Linear : Instr → Bool
  | .op .JUMP | .op .JUMPI | .op .RETURN | .op .INVALID => false
  | _ => true

theorem runInstr_linear {instruction : Instr} {s t : State}
    (hlinear : Linear instruction = true)
    (hresult : runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size ∧ t.halt = s.halt := by
  unfold runInstr at hresult
  split at hresult
  · split at hresult
    all_goals
      repeat' first | split at hresult | simp_all [Linear, Instr.size_push, Instr.size_op, Nat.add_comm]
    all_goals subst t; constructor <;> rfl
  · simp_all

/-- Only the final instruction may change control flow or halt. The location
certificates supply the actual artifact indices; these PC equations supply the
contiguous layout independently of the symbolic stack calculation. -/
def LinearPath {artifact : ProgramArtifact} {fork : Fork} :
    UInt256 → List (Located artifact fork) → Prop
  | _, [] => True
  | pc, [location] => UInt256.ofNat (artifact.instructionPC location.index) = pc
  | pc, location :: next :: rest =>
      UInt256.ofNat (artifact.instructionPC location.index) = pc ∧
      Linear location.instruction = true ∧
      LinearPath (pc + UInt256.ofNat location.instruction.size) (next :: rest)

private theorem runLocated_eq {artifact : ProgramArtifact} {fork : Fork}
    (location : Located artifact fork) (s : State)
    (hsize : artifact.code.size < 2 ^ 256)
    (hpc : s.pc = UInt256.ofNat (artifact.instructionPC location.index)) :
    runLocated location s = runInstr location.instruction s := by
  have hsmall : artifact.instructionPC location.index < 2 ^ 256 :=
    (artifact.instructionPC_le_code_size location.index).trans_lt hsize
  have hnat : s.pc.toNat = artifact.instructionPC location.index := by
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  simp [runLocated, hnat]

theorem run_linear {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (pc : UInt256) (s t : State)
    (hsize : artifact.code.size < 2 ^ 256)
    (hlayout : LinearPath pc path) (hpc : s.pc = pc)
    (hrunning : s.halt = .Running)
    (hrun : runInstructions (path.map Located.instruction) s = some t) :
    runLocatedBlock path s = some t := by
  induction path generalizing pc s t with
  | nil => simpa only [List.map_nil, runInstructions, runLocatedBlock] using hrun
  | cons location rest ih =>
      cases rest with
      | nil =>
          have hloc := runLocated_eq location s hsize (hpc.trans hlayout.symm)
          cases hstep : runInstr location.instruction s with
          | none => simp [runInstructions, hstep] at hrun
          | some middle =>
              simpa [runInstructions, runLocatedBlock, hloc, hstep] using hrun
      | cons next rest =>
          obtain ⟨hlocpc, hlinear, htail⟩ := hlayout
          have hloc := runLocated_eq location s hsize (hpc.trans hlocpc.symm)
          cases hstep : runInstr location.instruction s with
          | none => simp [runInstructions, hstep] at hrun
          | some middle =>
              have hm := runInstr_linear hlinear hstep
              have hmiddlePC : middle.pc = pc + UInt256.ofNat location.instruction.size := by
                rw [hm.1, hpc]
              have hmiddleRun : middle.halt = .Running := hm.2.trans hrunning
              have hrest : runInstructions
                  ((next :: rest).map Located.instruction) middle = some t := by
                simpa [runInstructions, hstep] using hrun
              have hresult := ih _ middle t htail hmiddlePC hmiddleRun hrest
              simpa only [runLocatedBlock, hloc, hstep, hmiddleRun] using hresult

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLocated

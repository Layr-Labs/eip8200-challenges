import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.Msize

set_option warningAsError true

/-!
# Straight-line evaluation extended with `MSIZE`

The shared evaluator `Challenge.EvmProof.Stepper.runInstr` does not expose `MSIZE`.
This module adds it locally: `runInstrX` agrees with `runInstr` on every other
instruction, and its `MSIZE` step is lifted to the real EVM relation through
`Msize.step`, which is derived directly from `StepRunning.msize`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper WindowNibbleKernel
open WindowTwentyOneLocated WindowTwentyOneBinding

/-- `runInstr` plus the `MSIZE` rule. -/
def runInstrX (instruction : Instr) (s : State) : Option State :=
  match instruction with
  | .op .MSIZE =>
      if s.stack.length < 1024 then
        some { s with
          stack := UInt256.ofNat (32 * s.activeWords.toNat) :: s.stack
          pc := s.pc.succ }
      else none
  | instruction => runInstr instruction s

def runInstructionsX : List Instr → State → Option State
  | [], state => some state
  | instruction :: rest, state => do
      let next ← runInstrX instruction state
      runInstructionsX rest next

theorem runInstructionsX_append (left right : List Instr) (state : State) :
    runInstructionsX (left ++ right) state =
      (runInstructionsX left state).bind (runInstructionsX right) := by
  induction left generalizing state with
  | nil => simp [runInstructionsX]
  | cons instruction rest ih =>
      cases h : runInstrX instruction state <;> simp [runInstructionsX, h, ih]

theorem runInstructionsX_append_some (left right : List Instr) (start middle finish : State)
    (hleft : runInstructionsX left start = some middle)
    (hright : runInstructionsX right middle = some finish) :
    runInstructionsX (left ++ right) start = some finish := by
  rw [runInstructionsX_append, hleft]
  exact hright

/-- Programs without `MSIZE` evaluate identically under both evaluators. -/
def hasMsize : List Instr → Bool
  | [] => false
  | .op .MSIZE :: _ => true
  | _ :: rest => hasMsize rest

theorem runInstrX_eq_runInstr (instruction : Instr) (s : State)
    (h : instruction ≠ .op .MSIZE) : runInstrX instruction s = runInstr instruction s := by
  unfold runInstrX
  split
  · exact absurd rfl h
  · rfl

theorem runInstructionsX_eq (program : List Instr) (hfree : hasMsize program = false)
    (state : State) : runInstructionsX program state = runInstructions program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      have hne : instruction ≠ .op .MSIZE := by
        intro heq
        subst heq
        simp [hasMsize] at hfree
      have hrest : hasMsize rest = false := by
        cases instruction with
        | push w v => simpa [hasMsize] using hfree
        | op op =>
            cases op <;> rename_i o <;> cases o <;> simp_all [hasMsize]
      simp [runInstructionsX, runInstructions, runInstrX_eq_runInstr instruction state hne, ih hrest]

/-- Decidable recognition of the one instruction the shared evaluator lacks. -/
def isMsize : Instr → Bool
  | .op .MSIZE => true
  | _ => false

theorem isMsize_true {instruction : Instr} (h : isMsize instruction = true) :
    instruction = .op .MSIZE := by
  cases instruction with
  | push w v => simp [isMsize] at h
  | op op => cases op <;> rename_i o <;> cases o <;> first | rfl | simp [isMsize] at h

theorem runInstrX_of_not_msize (instruction : Instr) (s : State)
    (h : isMsize instruction = false) : runInstrX instruction s = runInstr instruction s := by
  cases instruction with
  | push w v => rfl
  | op op => cases op <;> rename_i o <;> cases o <;> first | rfl | simp [isMsize] at h

theorem isMsize_op_false (op : Operation) (h : op ≠ .MSIZE) : isMsize (.op op) = false := by
  cases op <;> rename_i o <;> cases o <;> first | rfl | exact absurd rfl h

@[simp] theorem runInstrX_push (w : Fin 33) (v : UInt256) (s : State) :
    runInstrX (.push w v) s = runInstr (.push w v) s := rfl

@[simp] theorem runInstrX_op (op : Operation) (s : State) (h : op ≠ .MSIZE) :
    runInstrX (.op op) s = runInstr (.op op) s :=
  runInstrX_of_not_msize (.op op) s (isMsize_op_false op h)

theorem runInstrX_msize (s : State) :
    runInstrX (.op .MSIZE) s =
      if s.stack.length < 1024 then
        some { s with
          stack := UInt256.ofNat (32 * s.activeWords.toNat) :: s.stack
          pc := s.pc.succ }
      else none := rfl

theorem runInstrX_linear {instruction : Instr} {s t : State}
    (hlinear : Linear instruction = true)
    (hresult : runInstrX instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size ∧ t.halt = s.halt := by
  cases hm : isMsize instruction with
  | false =>
      rw [runInstrX_of_not_msize instruction s hm] at hresult
      exact runInstr_linear hlinear hresult
  | true =>
      have hins := isMsize_true hm
      subst hins
      rw [runInstrX_msize] at hresult
      split at hresult
      · simp only [Option.some.injEq] at hresult
        subst hresult
        refine ⟨?_, rfl⟩
        rfl
      · simp at hresult

theorem runInstrX_executionEnv {instruction : Instr} {s t : State}
    (hresult : runInstrX instruction s = some t) : t.executionEnv = s.executionEnv := by
  cases hm : isMsize instruction with
  | false =>
      rw [runInstrX_of_not_msize instruction s hm] at hresult
      exact runInstr_executionEnv hresult
  | true =>
      have hins := isMsize_true hm
      subst hins
      rw [runInstrX_msize] at hresult
      split at hresult
      · simp only [Option.some.injEq] at hresult
        subst hresult
        rfl
      · simp at hresult

/-- Located evaluation with the extended evaluator. -/
def runLocatedX {artifact : ProgramArtifact} {fork : Fork}
    (located : Located artifact fork) (s : State) : Option State :=
  if s.pc.toNat = artifact.instructionPC located.index then
    runInstrX located.instruction s
  else none

def runLocatedX_sound {artifact : ProgramArtifact} {fork : Fork}
    {located : Located artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocatedX located s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  cases hm : isMsize located.instruction with
  | false =>
      have hloc : runLocated located s = some t := by
        unfold runLocated
        unfold runLocatedX at hresult
        split at hresult
        · rename_i hpc
          rw [if_pos hpc, ← runInstrX_of_not_msize located.instruction s hm]
          exact hresult
        · simp at hresult
      exact runLocated_sound hcode hfork hloc hrun hnp
  | true =>
      unfold runLocatedX at hresult
      split at hresult
      · rename_i hpc
        have hwf : WellFormed s.fork located.instruction := by
          simpa [hfork] using located.wellFormed
        have hdec := decodes_of_artifact artifact s located.index located.instruction
          hcode hpc located.atIndex hwf
        have hins := isMsize_true hm
        rw [hins] at hdec hresult
        change s.decodedOp = some .MSIZE at hdec
        rw [runInstrX_msize] at hresult
        split at hresult
        · rename_i hcap
          simp only [Option.some.injEq] at hresult
          subst hresult
          exact Msize.step hdec hcap hrun hnp
        · simp at hresult
      · simp at hresult

theorem runLocatedX_executionEnv {artifact : ProgramArtifact} {fork : Fork}
    {located : Located artifact fork} {s t : State}
    (hresult : runLocatedX located s = some t) : t.executionEnv = s.executionEnv := by
  unfold runLocatedX at hresult
  split at hresult
  · exact runInstrX_executionEnv hresult
  · simp at hresult

def runLocatedBlockX {artifact : ProgramArtifact} {fork : Fork} :
    List (Located artifact fork) → State → Option State
  | [], s => some s
  | located :: rest, s =>
      match runLocatedX located s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runLocatedBlockX rest next
              | _ => none

def runLocatedBlockX_sound (artifact : ProgramArtifact) (fork : Fork)
    (path : List (Located artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork)
    (hresult : runLocatedBlockX path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) : GasSteps s t := by
  induction path generalizing s t with
  | nil =>
      simp [runLocatedBlockX] at hresult
      subst t
      exact GasSteps.refl s
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runLocatedX located s with
          | none => simp [runLocatedBlockX, hnext] at hresult
          | some next =>
              simp [runLocatedBlockX, hnext] at hresult
              subst t
              exact runLocatedX_sound hcode hfork hnext hrun hnp
      | cons nextLocated tail =>
          cases hnext : runLocatedX located s with
          | none => simp [runLocatedBlockX, hnext] at hresult
          | some next =>
              cases hnextRun : next.halt with
              | Running =>
                  simp [runLocatedBlockX, hnext, hnextRun] at hresult
                  have henv := runLocatedX_executionEnv hnext
                  have hnextCode : next.executionEnv.code = artifact.code := by rw [henv, hcode]
                  have hnextFork : next.fork = fork := by
                    change next.executionEnv.fork = fork
                    rw [henv]
                    exact hfork
                  have hnextNp : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig
                      next.executionEnv.fork next.executionEnv.codeAddr = false := by
                    rw [henv]
                    exact hnp
                  exact (runLocatedX_sound hcode hfork hnext hrun hnp).trans
                    (ih hnextCode hnextFork hresult hnextRun hnextNp)
              | Success => simp [runLocatedBlockX, hnext, hnextRun] at hresult
              | Returned => simp [runLocatedBlockX, hnext, hnextRun] at hresult
              | Reverted => simp [runLocatedBlockX, hnext, hnextRun] at hresult
              | Exception error => simp [runLocatedBlockX, hnext, hnextRun] at hresult

private theorem runLocatedX_eq {artifact : ProgramArtifact} {fork : Fork}
    (location : Located artifact fork) (s : State)
    (hsize : artifact.code.size < 2 ^ 256)
    (hpc : s.pc = UInt256.ofNat (artifact.instructionPC location.index)) :
    runLocatedX location s = runInstrX location.instruction s := by
  have hsmall : artifact.instructionPC location.index < 2 ^ 256 :=
    (artifact.instructionPC_le_code_size location.index).trans_lt hsize
  have hnat : s.pc.toNat = artifact.instructionPC location.index := by
    rw [hpc, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  simp [runLocatedX, hnat]

theorem run_linearX {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Located artifact fork)) (pc : UInt256) (s t : State)
    (hsize : artifact.code.size < 2 ^ 256)
    (hlayout : LinearPath pc path) (hpc : s.pc = pc)
    (hrunning : s.halt = .Running)
    (hrun : runInstructionsX (path.map Located.instruction) s = some t) :
    runLocatedBlockX path s = some t := by
  induction path generalizing pc s t with
  | nil => simpa only [List.map_nil, runInstructionsX, runLocatedBlockX] using hrun
  | cons location rest ih =>
      cases rest with
      | nil =>
          have hloc := runLocatedX_eq location s hsize (hpc.trans hlayout.symm)
          cases hstep : runInstrX location.instruction s with
          | none => simp [runInstructionsX, hstep] at hrun
          | some middle =>
              simpa [runInstructionsX, runLocatedBlockX, hloc, hstep] using hrun
      | cons next rest =>
          obtain ⟨hlocpc, hlinear, htail⟩ := hlayout
          have hloc := runLocatedX_eq location s hsize (hpc.trans hlocpc.symm)
          cases hstep : runInstrX location.instruction s with
          | none => simp [runInstructionsX, hstep] at hrun
          | some middle =>
              have hm := runInstrX_linear hlinear hstep
              have hmiddlePC : middle.pc = pc + UInt256.ofNat location.instruction.size := by
                rw [hm.1, hpc]
              have hmiddleRun : middle.halt = .Running := hm.2.trans hrunning
              have hrest : runInstructionsX
                  ((next :: rest).map Located.instruction) middle = some t := by
                simpa [runInstructionsX, hstep] using hrun
              have hresult := ih _ middle t htail hmiddlePC hmiddleRun hrest
              simpa only [runLocatedBlockX, hloc, hstep, hmiddleRun] using hresult

/-- Lift a symbolic run of a block that may contain `MSIZE`. -/
def Block.stepsX {artifact : ProgramArtifact} {fork : Fork} {pc : Nat}
    {instructions : List Instr} (block : Block artifact fork pc instructions)
    {s t : State} (env : Environment artifact fork s)
    (hpc : s.pc = UInt256.ofNat pc) (hrun : runInstructionsX instructions s = some t) :
    GasSteps s t := by
  have hraw : runInstructionsX (block.path.map Located.instruction) s = some t := by
    rw [block.instructions_eq]
    exact hrun
  exact runLocatedBlockX_sound artifact fork block.path env.code env.forkEq
    (run_linearX block.path _ s t env.sizeBound block.layout hpc env.running hraw)
    env.running env.noPrecompile

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

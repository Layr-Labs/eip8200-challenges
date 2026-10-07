import Challenge.Modexp.Submission.Proofs.Fast.TnR8FirstRow
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel
open R8ZeroFirstRow

/-- Exit by a code literal while keeping modulus[128] in the frame. -/
def quotientJump (destination : UInt256) : List Instr := [.push 2 destination, .op .JUMP]
def exitProgram (destination : UInt256) : List Instr :=
  (quotientA ++ quotientB) ++ quotientJump destination

theorem run_quotientJump (s : State)
    (pc c0 mu flag P hd tt next tn M m128 inv m0 m96 m64 m32 x destination : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    runInstructions (quotientJump destination)
      {s with pc := pc, stack := c0 :: mu :: endFrame flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest} =
    some {s with pc := destination,
                 stack := c0 :: mu :: endFrame flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest} := by
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  simp [quotientJump, endFrame, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    h17, h18, hjump]

theorem run_exit (s : State)
    (pc flag P hd tt next tn M m128 inv m0 m96 m64 m32 x destination : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    let t0 := MachineState.readWord s.memory 2336
    let mu := t0*inv
    runInstructions (exitProgram destination)
      {s with pc := pc, stack := endFrame flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest} =
    some {s with pc := destination,
                 stack := UInt256.addMod t0 (UInt256.mulMod m0 mu M) M :: mu ::
                   endFrame flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest} := by
  let t0 := MachineState.readWord s.memory 2336
  have h0 := run_quotientA s pc flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest hcap hact
  have h1 := run_quotientB s (advancePC 4 pc) (t0*inv) flag P hd tt next tn M m128 inv m0 m96 m64 m32 x rest hcap hact
  have h2 := run_quotientJump s (advancePC 12 pc)
    (UInt256.addMod t0 (UInt256.mulMod m0 (t0*inv) M) M) (t0*inv)
    flag P hd tt next tn M m128 inv m0 m96 m64 m32 x destination rest hcap hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  exact runInstructions_append_some _ _ _ _ _ h01 h2

/-- The first row's store as the M128 artifact spells it: all 7 cells use `cellsProgramM128 7`
(storing `t[1..7]` directly via `cellFastBC`), and the 3-byte suffix swaps the carry with
`tn = 0` and drops `bi`. -/
def finishStoreNarrow : List Instr :=
  [.op (.Swap ⟨5, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op .POP]

theorem run_finishStoreNarrow (s : State)
    (pc c bi P hd tt next tn M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) :
    runInstructions finishStoreNarrow
      {s with pc := pc, stack := c :: bi :: P :: hd :: tt :: next :: tn :: M ::
        target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest} =
    some {s with
      pc := advancePC 3 pc
      stack := tn :: P :: hd :: tt :: next :: c :: M ::
        target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest} := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [finishStoreNarrow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h14, h15, h16, advancePC]

def program (next destination : UInt256) : List Instr :=
  ((diagonalProgramM128 next ++ cellsProgramM128 7)
    ++ finishStoreNarrow) ++ exitProgram destination

def result (s : State) (hd next m128 destination inv m0 m96 m64 m32 : UInt256)
    (rest : List UInt256) : State :=
  let q := firstProduct s.memory
  let t0 := MachineState.readWord q.memory 2336
  let mu := t0 * inv
  {s with
    pc := destination
    memory := q.memory
    stack := UInt256.addMod t0 (UInt256.mulMod m0 mu maxWord) maxWord :: mu ::
      endFrame (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336)
        next q.carry maxWord m128 inv m0 m96 m64 m32
        (MachineState.readWord s.memory 2592) rest}

/-- The complete specialized first row for arbitrary incoming scratch memory
and zero incoming carry-register value. This is a universal instruction-semantics theorem. -/
theorem run_program (s : State)
    (pc hd ent next m128 destination inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    runInstructions (program next destination)
      (initial s pc hd ent (UInt256.ofNat 0) m128 inv m0 m96 m64 m32 aprev rest) =
      some (result s hd next m128 destination inv m0 m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x + x
  have h0 := run_diagonalM128 s pc hd ent next (UInt256.ofNat 0) m128 inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := run_cellsM128 s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next (UInt256.ofNat 0)
    (diagonal s.memory)
    (m128 :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 7 (by decide)
  have hpc1 : advancePC (28 * 7) (advancePC 30 pc) = advancePC 226 pc := by
    rw [← advancePC_add]
  rw [hpc1] at h1
  have h2 := run_finishStoreNarrow {s with memory := (firstProduct s.memory).memory} (advancePC 226 pc)
    (firstProduct s.memory).carry bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next (UInt256.ofNat 0) maxWord m128 inv m0
    (UInt256.ofNat 2336) m96 m64 m32 x rest hcap
  have hpc2 : advancePC 3 (advancePC 226 pc) = advancePC 229 pc := by
    rw [← advancePC_add]
  rw [hpc2] at h2
  have h3 := run_exit {s with memory := (firstProduct s.memory).memory} (advancePC 229 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next
    (firstProduct s.memory).carry maxWord m128 inv m0 m96 m64 m32 x destination rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3


/-- Binding to the exact preferred 5314-byte research runtime. -/
def block : Block TnM128CandidateArtifact.submissionArtifact .Osaka 5062
    (program (UInt256.ofNat 3599) (UInt256.ofNat 3841)) :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 4042 205 5062
    (program (UInt256.ofNat 3599) (UInt256.ofNat 3841))
    (by decide) (by rfl) (by rfl) (by decide)

#print axioms run_exit
#print axioms run_program
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow

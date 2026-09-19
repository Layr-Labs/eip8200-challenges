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

/-- The first row's store as the M128 artifact spells it: the `t[n-1]` address push is
narrowed to `PUSH2`, so the block is eight bytes rather than nine.  `TnR8FirstRow` keeps
the wide form for the other candidate artifact. -/
def finishStoreNarrow : List Instr :=
  [.op (.Swap ⟨6, by decide⟩), .op .POP,
   .push 2 2112, .op .MSTORE, .op .POP, .push 0 0]

theorem run_finishStoreNarrow (s : State)
    (pc c u bi P hd tt next tn M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions finishStoreNarrow
      {s with pc := pc, stack := c :: u :: bi :: P :: hd :: tt :: next :: tn :: M ::
        target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest} =
    some {s with
      pc := advancePC 8 pc
      stack := UInt256.ofNat 0 :: P :: hd :: tt :: next :: c :: M ::
        target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest
      memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded u.toNat 32) 2112} := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  have h17 : rest.length + 17 < 1024 := by omega
  have h18 : rest.length + 18 < 1024 := by omega
  have ht : (2112 : UInt256).toNat = 2112 := by decide
  have hT := activeWords_fix s 2112 32 (by decide) (by decide) hact
  have hz : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide
  simp [finishStoreNarrow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h14, h15, h16, h17, h18, State.activeWordsAfterUInt256, ht, hT, hz, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

def program (next destination : UInt256) : List Instr :=
  (((diagonalProgram next ++ cellsProgram 6) ++ cellAB (UInt256.ofNat (SquareModel.aAddr 8 7)))
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
and carry-register value. This is a universal instruction-semantics theorem. -/
theorem run_program (s : State)
    (pc hd ent next tn m128 destination inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code destination.toNat = true) :
    runInstructions (program next destination)
      (initial s pc hd ent tn m128 inv m0 m96 m64 m32 aprev rest) =
      some (result s hd next m128 destination inv m0 m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x + x
  let q6 := zeroRun (diagonal s.memory) bi 6
  let x7 := MachineState.readWord q6.memory (SquareModel.aAddr 8 7)
  have h0 := run_diagonal s pc hd ent next tn m128 inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := run_cells s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn
    (diagonal s.memory)
    (m128 :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 6 (by decide)
  have h1b := run_cellAB {s with memory := q6.memory} (advancePC 198 pc) q6.carry bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn maxWord (SquareModel.aAddr 8 7)
    (m128 :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) (by unfold SquareModel.aAddr; omega) hact
  have h2 := run_finishStoreNarrow {s with memory := q6.memory} (advancePC 221 pc)
    (R4Math.zCarry x7 bi q6.carry maxWord) (R4Math.zSum x7 bi q6.carry) bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn maxWord m128 inv m0
    (UInt256.ofNat 2336) m96 m64 m32 x rest hcap hact
  have h3 := run_exit {s with memory := (firstProduct s.memory).memory} (advancePC 229 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next
    (firstProduct s.memory).carry maxWord m128 inv m0 m96 m64 m32 x destination rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h01b := runInstructions_append_some _ _ _ _ _ h01 h1b
  have h012 := runInstructions_append_some _ _ _ _ _ h01b h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3


/-- Binding to the exact preferred 5314-byte research runtime. -/
def block : Block TnM128CandidateArtifact.submissionArtifact .Osaka 5072
    (program (UInt256.ofNat 3609) (UInt256.ofNat 3851)) :=
  WindowTwentyOneSlice.block TnM128CandidateArtifact.allWellFormed 4056 213 5072
    (program (UInt256.ofNat 3609) (UInt256.ofNat 3851))
    (by decide) (by rfl) (by rfl) (by decide)

#print axioms run_exit
#print axioms run_program
end Challenge.Modexp.Submission.Proofs.Fast.TnM128R8FirstRow

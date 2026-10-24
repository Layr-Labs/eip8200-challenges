import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! The current eight-limb first row, with its outgoing high word in the carry
register. Reuses the current frontier's diagonal and seven zero-accumulator
cells. The original memory at 2080 is arbitrary and remains untouched. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.TnR8FirstRow
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro SquareModel
open R8ZeroFirstRow

def finishStore : List Instr :=
  [.op (.Swap ⟨6, by decide⟩), .op .POP,
   .push 3 2112, .op .MSTORE, .op .POP, .push 0 0]

theorem run_finishStore (s : State)
    (pc c u bi P hd tt next tn M target inv m0 tl m96 m64 m32 x : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions finishStore
      {s with pc := pc, stack := c :: u :: bi :: P :: hd :: tt :: next :: tn :: M ::
        target :: inv :: m0 :: tl :: m96 :: m64 :: m32 :: x :: rest} =
    some {s with
      pc := advancePC 9 pc
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
  simp [finishStore, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    List.exchange, h14, h15, h16, h17, h18, State.activeWordsAfterUInt256, ht, hT, hz, advancePC]
  simp only [succ_eq_add, word_add_assoc]
  rfl

def program (next : UInt256) : List Instr :=
  (((diagonalProgram next ++ cellsProgram 6) ++ cellAB (UInt256.ofNat (SquareModel.aAddr 8 7)))
    ++ finishStore) ++ exitProgram

def result (s : State) (hd next target inv m0 m96 m64 m32 : UInt256)
    (rest : List UInt256) : State :=
  let q := firstProduct s.memory
  let t0 := MachineState.readWord q.memory 2336
  let mu := t0 * inv
  {s with
    pc := target
    memory := q.memory
    stack := UInt256.addMod t0 (UInt256.mulMod m0 mu maxWord) maxWord :: mu ::
      endFrame (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336)
        next q.carry maxWord target inv m0 m96 m64 m32
        (MachineState.readWord s.memory 2592) rest}

/-- The complete specialized first row for arbitrary incoming scratch memory
and carry-register value. This is a universal instruction-semantics theorem. -/
theorem run_program (s : State)
    (pc hd ent next tn target inv m0 m96 m64 m32 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code target.toNat = true) :
    runInstructions (program next)
      (initial s pc hd ent tn target inv m0 m96 m64 m32 aprev rest) =
      some (result s hd next target inv m0 m96 m64 m32 rest) := by
  let x := MachineState.readWord s.memory 2592
  let bi := x + x
  let q6 := zeroRun (diagonal s.memory) bi 6
  let x7 := MachineState.readWord q6.memory (SquareModel.aAddr 8 7)
  have h0 := run_diagonal s pc hd ent next tn target inv m0 (UInt256.ofNat 2336)
    m96 m64 m32 aprev rest hcap hact
  have h1 := run_cells s (advancePC 30 pc) bi (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn
    (diagonal s.memory)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) hact 6 (by decide)
  have h1b := run_cellAB {s with memory := q6.memory} (advancePC 198 pc) q6.carry bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn maxWord (SquareModel.aAddr 8 7)
    (target :: inv :: m0 :: UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: x :: rest)
    (by simp only [List.length_cons]; omega) (by unfold SquareModel.aAddr; omega) hact
  have h2 := run_finishStore {s with memory := q6.memory} (advancePC 221 pc)
    (R4Math.zCarry x7 bi q6.carry maxWord) (R4Math.zSum x7 bi q6.carry) bi
    (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next tn maxWord target inv m0
    (UInt256.ofNat 2336) m96 m64 m32 x rest hcap hact
  have h3 := run_exit {s with memory := (firstProduct s.memory).memory} (advancePC 230 pc)
    (UInt256.ofNat 0) (UInt256.ofNat 2592) hd (UInt256.ofNat 2336) next
    (firstProduct s.memory).carry maxWord target inv m0 m96 m64 m32 x rest hcap hact hjump
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h01b := runInstructions_append_some _ _ _ _ _ h01 h1b
  have h012 := runInstructions_append_some _ _ _ _ _ h01b h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

/-- Flushing the first row's register recovers the frontier's first-row memory
exactly, including all bytes outside the accumulator. -/
theorem materialize_firstProduct (mem : ByteArray) :
    TnCacheMemory.lift (firstProduct mem).memory (firstProduct mem).carry =
      firstMemory mem := rfl

/-- The current first-row result is recovered by materializing only the cached
word. The reference frame's former stride slot receives the same carry value. -/
theorem result_materialized (s : State)
    (hd next target inv m0 m96 m64 m32 : UInt256) (rest : List UInt256) :
    {result s hd next target inv m0 m96 m64 m32 rest with
      memory := TnCacheMemory.lift (firstProduct s.memory).memory (firstProduct s.memory).carry} =
    R8ZeroFirstRow.result s hd next (firstProduct s.memory).carry target
      inv m0 m96 m64 m32 rest := by
  have ht : MachineState.readWord (firstMemory s.memory) 2336 =
      MachineState.readWord (firstProduct s.memory).memory 2336 :=
    TnCacheMemory.read_lift_outside _ _ 2336 (Or.inr (by decide))
  simp only [result, R8ZeroFirstRow.result, materialize_firstProduct, ht]

def block : Block TnCandidateArtifact.submissionArtifact .Osaka 4917
    (program (UInt256.ofNat 3420)) :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 3730 213 4917
    (program (UInt256.ofNat 3420))
    (by decide) (by rfl) (by rfl) (by decide)

#print axioms run_program
#print axioms materialize_firstProduct
#print axioms result_materialized
end Challenge.Modexp.Submission.Proofs.Fast.TnR8FirstRow

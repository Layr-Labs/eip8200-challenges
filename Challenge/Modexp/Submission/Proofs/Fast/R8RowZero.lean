import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.R8ZeroFirstRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! # The eight-limb first row

The first row of the eight-limb square is one straight-line block at pc 5090 (instruction
indices 3907..4120): the diagonal cell, seven direct zero-accumulator cells, the carry
store and the quotient/exit.  Its semantics are `R8ZeroFirstRow.run_program`; this module
binds that program to the submitted artifact and restates the entry in the row-frame
vocabulary of the square chain (`outState`). -/

namespace Challenge.Modexp.Submission.Proofs.Fast.R8RowZero
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel CarryRowModel CarryScratchAgreement

def program : List Instr := R8ZeroFirstRow.program (UInt256.ofNat 3586)

def block : Block Artifact.submissionArtifact .Osaka 5091 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3905 214 5091 program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)

theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5091 = true :=
  Artifact.isValidJumpDest_index 3905 (by rfl)

/-- The second-loop entry the row jumps to (`l2Target 8`). -/
theorem jumpDestL2 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3837 = true :=
  Artifact.isValidJumpDest_index 2892 (by rfl)

theorem l2Target_eight_toNat : (l2Target 8).toNat = 3837 := by decide

theorem allOnes_eq_maxWord : allOnes = maxWord := rfl

/-- The chain's row-0 entry frame (`tl = 2336`, the eight-limb `T` base) is the new row's
`initial` frame. -/
theorem entry_eq (s : State) (mem : ByteArray) (pc hd : UInt256) (e : Nat)
    (inv m0 m96 m64 m32 aprev : UInt256) (rest : List UInt256) :
    ({ outState s mem 2368 8 0 hd (UInt256.ofNat e) inv m0
        (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest) with pc := pc } : State) =
      R8ZeroFirstRow.initial { s with memory := mem } pc hd (UInt256.ofNat e) negative32
        (l2Target 8) inv m0 m96 m64 m32 aprev rest := by
  simp only [outState, R8ZeroFirstRow.initial, ptrAt_zero, allOnes_eq_maxWord]
  rfl

/-- The row from the chain's entry state: `R8ZeroFirstRow.run_program` in the frame
vocabulary of the square rows. -/
theorem run_rowZero (s : State) (mem : ByteArray) (pc hd : UInt256) (e : Nat)
    (inv m0 m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hact : 88 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 3837 = true) :
    runInstructions program
      { outState s mem 2368 8 0 hd (UInt256.ofNat e) inv m0
        (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest) with pc := pc } =
    some (R8ZeroFirstRow.result { s with memory := mem } hd (UInt256.ofNat 3586) negative32
      (l2Target 8) inv m0 m96 m64 m32 rest) := by
  have hj : Decode.isValidJumpDest ({ s with memory := mem } : State).executionEnv.code
      (l2Target 8).toNat = true := by
    rw [l2Target_eight_toNat]; exact hjump
  rw [entry_eq]
  exact R8ZeroFirstRow.run_program { s with memory := mem } pc hd (UInt256.ofNat e)
    (UInt256.ofNat 3586) negative32 (l2Target 8) inv m0 m96 m64 m32 aprev rest hcap hact hj

def gasSteps_prologue (s : State) (mem : ByteArray) (e : Nat)
    (inv m0 m96 m64 m32 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1002) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      { outState s mem 2368 8 0 (UInt256.ofNat 4234) (UInt256.ofNat e) inv m0
        (UInt256.ofNat 2336 :: m96 :: m64 :: m32 :: aprev :: rest) with pc := UInt256.ofNat 5091 }
      (R8ZeroFirstRow.result { s with memory := mem } (UInt256.ofNat 4234) (UInt256.ofNat 3586)
        negative32 (l2Target 8) inv m0 m96 m64 m32 rest) :=
  SquareRow.stepsOf block
    (run_rowZero s mem (UInt256.ofNat 5091) (UInt256.ofNat 4234) e inv m0 m96 m64 m32 aprev rest
      hcap hact (by rw [hcode]; exact jumpDestL2)) rfl hcode hfork hrun hnp

#print axioms run_rowZero
end Challenge.Modexp.Submission.Proofs.Fast.R8RowZero

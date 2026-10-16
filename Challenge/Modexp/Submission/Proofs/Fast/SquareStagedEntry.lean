import Challenge.Modexp.Submission.Proofs.Fast.SquareRow

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached

/-- The square entry: row head 4293, frame word 3 := `mem[0xc0]` (`n1`; p2), and the row pointer
`q := 0x1e0 - base` (zneg2: `-0x100` for eight limbs, the R4 marker `-0x80` for four). -/
def program : List Instr :=
  [.op .JUMPDEST, .push 2 5297, .op (.Swap ⟨1, by decide⟩), .op .POP,
   .push 1 192, .op .MLOAD, .op (.Swap ⟨2, by decide⟩), .op .POP,
   .push 2 480, .op .SUB]

def block : Block Artifact.submissionArtifact .Osaka 4245 program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 10 4245 program
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
    (UInt256.ofNat 4245).toNat = true :=
  Artifact.isValidJumpDest_index 3303 (by rfl)

/-- The entry's row pointer word. -/
def qWord (n : Nat) : UInt256 := UInt256.ofNat 480 - UInt256.ofNat (512 + 32 * n - 32)

theorem qWord_eight : qWord 8 = UInt256.ofNat (2^256 - 256) := by decide

theorem qWord_four : qWord 4 = UInt256.ofNat (2^256 - 128) := by decide

/-- The state at H1 (4597). -/
def h1State (s : State) (mem : ByteArray) (n : Nat) (ent w5 inv m0 : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4260
           stack := [qWord n, UInt256.ofNat 5297, MachineState.readWord mem 192, ent, w5, allOnes,
             MachineState.readWord mem 128, inv, m0] ++ rest
           memory := mem }

theorem run_entry (s : State) (mem : ByteArray) (n : Nat)
    (ent w5 inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1012)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions program
      (outState s mem 512 n 0 (UInt256.ofNat 4245) ent w5 inv m0 rest) =
    some (h1State s mem n ent w5 inv m0 rest) := by
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have hactM := Csub.activeWords_fix s 192 32 (by decide) (by decide) hact
  simp [program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    outState, h1State, qWord, ptrAt_zero, h9, h10, hactM, State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_entry (s : State) (mem : ByteArray) (n : Nat)
    (ent w5 inv m0 : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1012)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (outState s mem 512 n 0 (UInt256.ofNat 4245) ent w5 inv m0 rest)
      (h1State s mem n ent w5 inv m0 rest) :=
  block.steps (SquareRow.environment _ hcode hfork hrun hnp) rfl
    (run_entry s mem n ent w5 inv m0 rest hcap hact)

end Challenge.Modexp.Submission.Proofs.Fast.SquareStagedEntry

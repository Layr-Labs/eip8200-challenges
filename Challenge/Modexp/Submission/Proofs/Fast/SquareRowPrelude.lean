import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# The `sq_row` prologue of the square rows (sqCP1m, new idx 3604..3653, pc 0x1266)

`sq_row` is the row head `hd = 4710` of a square call.  On the kernel row frame
`[P, hd, pb-32, ent, -32, M, l2T, …, aprev, …]` (`P` = pointer to `x = a_i`,
slot 14 = `aprev`) it

* loads `x`, parks it in slot 14 (`DUP1 SWAP15`), and computes `tb = SGT 0 aprev`;
* computes `f = x + tb`, `b2 = f + x`, `lo = x * f`, `hi` (512-bit high word via
  `MULMOD … 2^256-1`), stores `s = lo + t_i` at `P + 0x1840 = tAddr n i` and leaves the
  carry `C = [s < lo] + hi` above `b2`;
* advances the frame's `ent` slot by 38 and jumps to the old `ent` — the entry of the
  first-loop block that performs limb step `i + 1` (`KernelChain`).

The memory/carry it produces is exactly WP-S1's `SquareModel.sqPro mem n i tb`.

The block is split at the `SGT` (the shared stepper has no `SGT` case): block A
(idx 3604..3609, pc 4710, 6 instructions), `SgtStep.gasSteps_sqRowSgt_framed`
(idx 3610, pc 4716), block B (idx 3611..3653, pc 4717, 43 instructions; its
`runInstructions` proof is split into five sub-programs).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

/-! ## Programs -/

/-- `JUMPDEST DUP1 MLOAD DUP1 SWAP15 PUSH0` (idx 3604..3609). -/
def programA : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩), .push 0 0]

/-- `DUP2 ADD DUP2 DUP2 ADD SWAP2 DUP9 DUP3 DUP3 MULMOD` (idx 3611..3620). -/
def programB1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .MULMOD]

/-- `SWAP2 DUP2 DUP2 LT SWAP2 MUL SWAP2 SUB DUP2 DUP2 LT DUP3 SWAP2 SUB SUB` (idx 3621..3635). -/
def programB2 : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

/-- `SWAP1 DUP4 PUSH2 0x1840 ADD` (idx 3636..3639). -/
def programB3a : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨3, by decide⟩), .push 2 1600, .op .ADD]

/-- `DUP1 MLOAD DUP3 ADD DUP1 SWAP2 MSTORE LT ADD` (idx 3640..3648). -/
def programB3b : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .MSTORE, .op .LT, .op .ADD]

/- `PUSH1 0x26 DUP7 ADD SWAP6 JUMP` (idx 3649..3653). -/
/-- Fused B2/B3; the widened PUSH preserves the byte end at pc 4757. -/
def programB23 : List Instr :=
  [.op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB,
   .op (.Dup ⟨3, by decide⟩), .push 4 1600, .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

def programB4 : List Instr :=
  [.push 1 38, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .JUMP]

/-- Everything after the `SGT` (idx 3611..3653). -/
def programB : List Instr :=
  (programB1 ++ programB23) ++ programB4

/-! ## Location certificates -/

def blockA : Block Artifact.submissionArtifact .Osaka 4710 programA :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3590 6 4710 programA
    (by decide) (by rfl) (by rfl) (by decide)

def blockB : Block Artifact.submissionArtifact .Osaka 4717 programB :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 41 4717 programB
    (by decide) (by rfl) (by rfl) (by decide)

/-- `sq_row` itself is a jump destination (the frame's row head for square calls). -/
theorem jumpDest4710 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4710 = true :=
  Artifact.isValidJumpDest_index 3590 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
      rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `Block.steps` with the symbolic run first, so that the block's start state is read off
the run (used on record-update states). -/
def stepsOf {pc : Nat} {instructions : List Instr}
    (block : Block Artifact.submissionArtifact .Osaka pc instructions) {s t : State}
    (hrun' : runInstructions instructions s = some t) (hpc : s.pc = UInt256.ofNat pc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  block.steps (environment s hcode hfork hrun hnp) hpc hrun'

/-! ## Symbolic runs (generic stacks) -/

theorem run_A (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions programA
      { s with pc := UInt256.ofNat 4710,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 4716,
                  stack := ⟨0⟩ :: aprev :: MachineState.readWord s.memory P.toNat :: P :: hd :: w3 ::
                    ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 :: w13 ::
                    MachineState.readWord s.memory P.toNat :: rest } := by
  have h14 : rest.length + 14 < 1024 := by omega
  have h15 : rest.length + 15 < 1024 := by omega
  have h16 : rest.length + 16 < 1024 := by omega
  simp [programA, runInstructions, Challenge.EvmProof.Stepper.runInstr, h14, h15, h16,
    State.activeWordsAfterUInt256, hact, List.exchange]
  decide

theorem run_B1 (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1010) :
    runInstructions programB1
      { s with pc := UInt256.ofNat 4717,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 4727,
                  stack := UInt256.mulMod x (x + tb) M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
                    w3 :: ent :: w5 :: M :: rest } := by
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  have h11 : rest.length + 11 < 1024 := by omega
  have h12 : rest.length + 12 < 1024 := by omega
  simp [programB1, runInstructions, Challenge.EvmProof.Stepper.runInstr, h8, h9, h10, h11, h12,
    List.exchange]
  decide

theorem run_B2 (s : State) (mmr x f b2 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016) :
    runInstructions programB2
      { s with pc := UInt256.ofNat 4727, stack := mmr :: x :: f :: b2 :: rest } =
    some { s with pc := UInt256.ofNat 4742,
                  stack := (((mmr - UInt256.lt f x) - UInt256.lt (mmr - UInt256.lt f x) (x * f)) - x * f) ::
                    (x * f) :: b2 :: rest } := by
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [programB2, runInstructions, Challenge.EvmProof.Stepper.runInstr, h3, h4, h5, h6,
    List.exchange]
  decide

theorem run_B3a (s : State) (hi lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016) :
    runInstructions programB3a
      { s with pc := UInt256.ofNat 4742, stack := hi :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4748,
                  stack := ((1600 : UInt256) + P) :: lo :: hi :: b2 :: P :: rest } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  simp [programB3a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h4, h5, h6,
    List.exchange]
  decide

theorem run_B3b (s : State) (tA lo hi b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1016)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions programB3b
      { s with pc := UInt256.ofNat 4748, stack := tA :: lo :: hi :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4757,
                  stack := (UInt256.lt (lo + MachineState.readWord s.memory tA.toNat) lo + hi) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  simp [programB3b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h4, h5, h6, h7,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

opaque fused_carry_eq (carry borrow a lo : UInt256) :
    (carry - (borrow - a)) - lo = carry + ((a - borrow) - lo) := by
  apply Challenge.EvmProof.Word.word_ext
  have hc : carry.toNat < 2 ^ 256 := carry.val.isLt
  have hb : borrow.toNat < 2 ^ 256 := borrow.val.isLt
  have ha : a.toNat < 2 ^ 256 := a.val.isLt
  have hl : lo.toNat < 2 ^ 256 := lo.val.isLt
  simp only [Challenge.EvmProof.Word.word_toNat_sub, Challenge.EvmProof.Word.word_toNat_add]
  omega


end Challenge.Modexp.Submission.Proofs.Fast.SquareRow

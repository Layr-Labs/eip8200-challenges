import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Mathlib.Algebra.Group.Fin.Basic

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# The `sq_row` prologue of the square rows (sqCP1m, new idx 3559..3840, pc 0x1266)

`sq_row` is the row head `hd = 4801` of a square call.  On the kernel row frame
`[P, hd, pb-32, ent, -32, M, l2T, …, aprev, …]` (`P` = pointer to `x = a_i`,
slot 14 = `aprev`) it

* loads `x`, parks it in slot 14 (`DUP1 SWAP15`), and computes `tb = SGT 0 aprev`;
* computes `f = x + tb`, `b2 = f + x`, `lo = x * f`, `hi` (2368-bit high word via
  `MULMOD … 2^256-1`), stores `s = lo + t_i` at `P + 0x1840 = tAddr n i` and leaves the
  carry `C = [s < lo] + hi` above `b2`;
* advances the frame's `ent` slot by 37 and jumps to the old `ent` — the entry of the
  first-loop block that performs limb step `i + 1` (`KernelChain`).

The memory/carry it produces is exactly WP-S1's `SquareModel.sqPro mem n i tb`.

The block is split at the `SGT` (the shared stepper has no `SGT` case): block A
(idx 3559..3698, pc 4801, 6 instructions), `SgtStep.gasSteps_sqRowSgt_framed`
(idx 3739, pc 4807), block B (idx 3700..3840, pc 4927, 43 instructions; its
`runInstructions` proof is split into five sub-programs).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

/-! ## Programs -/

/-- `JUMPDEST DUP1 MLOAD DUP1 SWAP15 PUSH0` (idx 3559..3698). -/
def programA : List Instr :=
  [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨14, by decide⟩), .push 0 0]

/-- `DUP2 ADD DUP2 DUP2 ADD SWAP2 DUP9 DUP3` (idx 3700..3721). -/
def programB1 : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨8, by decide⟩), .op (.Dup ⟨2, by decide⟩)]

/-- `SWAP2 DUP2 DUP2 LT SWAP2 MUL SWAP2 SUB DUP2 DUP2 LT DUP3 SWAP2 SUB SUB` (idx 3658..3840). -/
def programB2 : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT,
   .op (.Swap ⟨1, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩), .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op (.Dup ⟨2, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .SUB, .op .SUB]

/-- `SWAP1 DUP4 PUSH2 0x1840 ADD` (idx 3840..3840). -/
def programB3a : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .push 2 256, .op (.Dup ⟨4, by decide⟩), .op .SUB]

/-- `DUP1 MLOAD DUP3 ADD DUP1 SWAP2 MSTORE LT ADD` (idx 3840..3648). -/
def programB3b : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .op .MSTORE, .op .LT, .op .ADD]

/-- `PUSH1 0x26 DUP7 ADD SWAP6 JUMP` (idx 3840..3840). -/
def programB4 : List Instr :=
  [.push 1 37, .op (.Dup ⟨6, by decide⟩), .op .ADD, .op (.Swap ⟨5, by decide⟩), .op .JUMP]

/-- Fuse the diagonal high-word borrow with the stored-low-word carry.
The two bytes it saves are re-placed as unreachable `JUMPDEST`s after the row's final
`JUMP` (pc 5032..5032), so every pc and instruction index from 43 (idx 3720) on is unchanged. -/
def programB23 : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL,
   .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .push 2 256, .op (.Dup ⟨4, by decide⟩), .op .SUB,
   .op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

/-- Everything after the `SGT` (idx 3700..3840). -/
def programB : List Instr :=
  (programB1 ++ programB23) ++ programB4

/-! ## Symbolic runs (generic stacks) -/

theorem run_A (s : State) (P hd w3 ent w5 M w7 w8 w9 w10 w11 w12 w13 aprev : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat P.toNat 32) =
      s.activeWords) :
    runInstructions programA
      { s with pc := UInt256.ofNat 4093,
               stack := P :: hd :: w3 :: ent :: w5 :: M :: w7 :: w8 :: w9 :: w10 :: w11 :: w12 ::
                 w13 :: aprev :: rest } =
    some { s with pc := UInt256.ofNat 4099,
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
      { s with pc := UInt256.ofNat 4100,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := UInt256.ofNat 4108,
                  stack := (x + tb) :: M :: x :: (x + tb) :: ((x + tb) + x) :: P :: hd ::
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
      { s with pc := UInt256.ofNat 4111, stack := mmr :: x :: f :: b2 :: rest } =
    some { s with pc := UInt256.ofNat 4126,
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
      { s with pc := UInt256.ofNat 4126, stack := hi :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4132,
                  stack := (P - (256 : UInt256)) :: lo :: hi :: b2 :: P :: rest } := by
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
      { s with pc := UInt256.ofNat 4132, stack := tA :: lo :: hi :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4141,
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

theorem run_B4 (s : State) (C b2 P hd w3 ent : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1015)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB4
      { s with pc := UInt256.ofNat 4137, stack := C :: b2 :: P :: hd :: w3 :: ent :: rest } =
    some { s with pc := ent,
                  stack := C :: b2 :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: rest } := by
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  simp [programB4, runInstructions, Challenge.EvmProof.Stepper.runInstr, h6, h7, h8,
    List.exchange, hjump]
  rfl

/-- The fused borrow up to the store address (pc 4997..5014). -/
def programB23a : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MUL,
   .op (.Swap ⟨4, by decide⟩), .op .LT, .op (.Swap ⟨2, by decide⟩), .op .MULMOD,
   .op .SUB,
   .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB,
   .push 2 256, .op (.Dup ⟨4, by decide⟩), .op .SUB]

/-- Load/add/store and the two-subtraction carry (pc 5014..2336). -/
def programB23b : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op .MLOAD, .op (.Dup ⟨3, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .GT, .op .SUB, .op .SUB]

theorem programB23_split : programB23 = programB23a ++ programB23b := rfl

private theorem carryReassociate (c a b lo : UInt256) :
    (c - (b - a)) - lo = c + ((a - b) - lo) := by
  change UInt256.mk ((c.val - (b.val - a.val)) - lo.val) =
    UInt256.mk (c.val + ((a.val - b.val) - lo.val))
  congr 1
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
  exact add_assoc _ _ _

private theorem gt_eq_lt (a b : UInt256) : UInt256.gt a b = UInt256.lt b a := by
  rfl

private theorem mul_comm' (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

theorem run_B23a (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013) :
    runInstructions programB23a
      { s with pc := UInt256.ofNat 4108, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4126,
                  stack := (P - (256 : UInt256)) ::
                    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) -
                      (UInt256.mulMod x f M - UInt256.lt f x)) ::
                    (f * x) :: b2 :: P :: rest } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  have h10 : rest.length + 10 < 1024 := by omega
  simp [programB23a, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    List.exchange]
  decide

theorem run_B23b (s : State) (tA d lo b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1014)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat tA.toNat 32) =
      s.activeWords) :
    runInstructions programB23b
      { s with pc := UInt256.ofNat 4126, stack := tA :: d :: lo :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4137,
                  stack := ((UInt256.gt lo (lo + MachineState.readWord s.memory tA.toNat) - d) - lo) ::
                    b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded (lo + MachineState.readWord s.memory tA.toNat).toNat 32)
                    tA.toNat } := by
  have h1 : rest.length + 1 < 1024 := by omega
  have h2 : rest.length + 2 < 1024 := by omega
  have h3 : rest.length + 3 < 1024 := by omega
  have h4 : rest.length + 4 < 1024 := by omega
  have h5 : rest.length + 5 < 1024 := by omega
  have h6 : rest.length + 6 < 1024 := by omega
  have h7 : rest.length + 7 < 1024 := by omega
  have h8 : rest.length + 8 < 1024 := by omega
  have h9 : rest.length + 9 < 1024 := by omega
  simp [programB23b, runInstructions, Challenge.EvmProof.Stepper.runInstr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    List.exchange, State.activeWordsAfterUInt256, hact]
  decide

/-- The fused program preserves the original carry formula for arbitrary words. -/
theorem run_B23 (s : State) (x f M b2 P : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1013)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (P - (256 : UInt256)).toNat 32) = s.activeWords) :
    runInstructions programB23
      { s with pc := UInt256.ofNat 4108, stack := f :: M :: x :: f :: b2 :: P :: rest } =
    some { s with pc := UInt256.ofNat 4137,
                  stack := (UInt256.lt (x * f + MachineState.readWord s.memory (P - (256 : UInt256)).toNat)
                      (x * f) + (((UInt256.mulMod x f M - UInt256.lt f x) -
                        UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (x * f)) - x * f)) :: b2 :: P :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (x * f + MachineState.readWord s.memory (P - (256 : UInt256)).toNat).toNat 32)
                    (P - (256 : UInt256)).toNat } := by
  have ha := run_B23a s x f M b2 P rest hcap
  have hb := run_B23b s (P - (256 : UInt256))
    (UInt256.lt (UInt256.mulMod x f M - UInt256.lt f x) (f * x) - (UInt256.mulMod x f M - UInt256.lt f x))
    (f * x) b2 P rest (by omega) hact
  rw [programB23_split, runInstructions_append_some _ _ _ _ _ ha hb, carryReassociate, gt_eq_lt,
    mul_comm' f x]

/-- The word after the prologue: `lo = x * (x + tb)`. -/
abbrev loOf (x tb : UInt256) : UInt256 := x * (x + tb)

/-- The high word as the machine computes it (with the modulus word `M`). -/
abbrev hiOf (x tb M : UInt256) : UInt256 :=
  ((UInt256.mulMod x (x + tb) M - UInt256.lt (x + tb) x) -
    UInt256.lt (UInt256.mulMod x (x + tb) M - UInt256.lt (x + tb) x) (x * (x + tb))) - x * (x + tb)

/-- Block B on a generic stack: from the `SGT` result `tb` to the jump to `ent`. -/
theorem run_B (s : State) (tb x P hd w3 ent w5 M : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (P - (256 : UInt256)).toNat 32) = s.activeWords)
    (hjump : Decode.isValidJumpDest s.executionEnv.code ent.toNat = true) :
    runInstructions programB
      { s with pc := UInt256.ofNat 4100,
               stack := tb :: x :: P :: hd :: w3 :: ent :: w5 :: M :: rest } =
    some { s with pc := ent,
                  stack := (UInt256.lt (loOf x tb + MachineState.readWord s.memory (P - (256 : UInt256)).toNat)
                      (loOf x tb) + hiOf x tb M) ::
                    ((x + tb) + x) :: P :: hd :: w3 :: (ent + UInt256.ofNat 37) :: w5 :: M :: rest
                  memory := MachineState.writeBytes s.memory
                    (Data.Bytes.natToBytesPadded
                      (loOf x tb + MachineState.readWord s.memory (P - (256 : UInt256)).toNat).toNat 32)
                    (P - (256 : UInt256)).toNat } := by
  have h1 := run_B1 s tb x P hd w3 ent w5 M rest (by omega)
  have h2 := run_B23 s x (x + tb) M ((x + tb) + x) P
    (hd :: w3 :: ent :: w5 :: M :: rest) (by simp only [List.length_cons]; omega) hact
  have h5 := run_B4
    { s with memory := (MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded
        (loOf x tb + MachineState.readWord s.memory (P - (256 : UInt256)).toNat).toNat 32)
      (P - (256 : UInt256)).toNat) }
    (UInt256.lt (loOf x tb + MachineState.readWord s.memory (P - (256 : UInt256)).toNat)
      (loOf x tb) + hiOf x tb M) ((x + tb) + x) P hd w3 ent (w5 :: M :: rest)
    (by simp only [List.length_cons]; omega) hjump
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ h1 h2) h5

/-! ## The prologue on the kernel row frame -/

/-- The row pointer of square row `i` is the address of `a_i`. -/
theorem ptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 8) :
    (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)).toNat = aAddr n i := by
  rw [ptrAt_toNat _ _ (by omega) (by omega), aAddr]
  omega

/-- ... and `P + 0x1840` is the address of `t_i`. -/
theorem tptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 8) :
    (UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i) - (256 : UInt256)).toNat = tAddr n i  := by
  have hp : UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i) = UInt256.ofNat (aAddr n i) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [ptr_toNat n i hi hn, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by unfold aAddr; omega)]
  rw [hp, show (256 : UInt256) = UInt256.ofNat 256 by decide,
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by unfold aAddr; omega) (by unfold aAddr; omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by unfold aAddr; omega)]
  unfold aAddr tAddr
  omega

theorem push0_eq : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide


#print axioms run_A
#print axioms run_B
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareTrace

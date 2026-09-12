import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopRuns
import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopAgain
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The in-kernel squaring loop: `k` squares in one call

For `n ∈ {4, 8}` the caller stores the number of squares in memory word 9280 and enters the
kernel once.  Each round runs the `n` square rows, and `sq_exit` decrements the counter:
while it stays non-zero the conditional subtraction runs as a subroutine and `again`
rebuilds the row-0 state for the next square; on zero the frame's `ret` slot is rewritten to
`after_sq` (3243) and the call leaves through the ordinary exit.

`gasSteps_squareLoop` is the whole call; `SquareLoopMem.sqLoopMem` is its memory and
`SquareLoopMem.sqLoopMem_represents` its value (`k` Montgomery squares).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CiosCached SquareModel SquareResult SquareRow SquareRows
open SquareLoopBlocks StagedOperand CarryRowModel CiosCachedMidMemory

/-! The memory model and its caller-facing lemmas live in `SquareLoopMem`; they are
re-exported here so that the caller side only needs `SquareLoop`. -/
export Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem (sqLoopMem sqLoopMem_zero sqLoopMem_succ sqLoopMem_represents
  sqLoopMem_frame sqLoopMem_fastRepresents_outside sqLoopMem_readWord_outside
  sqLoopMem_readWord_high)

/-! ## The row-0 memory of a square -/

/-- The memory the kernel's `setup` — and the loop's `again` — hands to row 0: the operand
staged at 8960 and the accumulator zeroed. -/
def rowZero (s : State) (mem : ByteArray) (n : Nat) : ByteArray :=
  mpZeroed s (stage mem 2048 n) n

theorem rowZero_eq_input (s : State) (mem : ByteArray) (n : Nat) (hn : n = 4 ∨ n = 8) :
    mpZeroed s (inputMemory mem 2048 n) n = rowZero s mem n := by
  rw [rowZero, show inputMemory mem 2048 n = stage mem 2048 n from by
    unfold inputMemory; rw [if_pos hn]]

theorem sqRound_eq (s : State) (mem : ByteArray) (n c : Nat) :
    SquareLoopMem.sqRound s n c mem =
      Csub.csResultMemory (countMem (sqRowsCarry (rowZero s mem n) n n) c) n 2048 := rfl

/-- Configuration words of the call memory survive staging, zeroing, the rows and the
counter store. -/
theorem read_prefix (s : State) (M : ByteArray) (n c addr : Nat) (hn32 : n ≤ 32)
    (hfast : n = 4 ∨ n = 8) (hd : addr + 32 ≤ 8192 ∨ 9312 ≤ addr) :
    MachineState.readWord (countMem (sqRowsCarry (rowZero s M n) n n) c) addr =
      MachineState.readWord M addr := by
  rw [readWord_countMem_disjoint _ c addr (by omega),
    readWord_sqRowsCarry _ n addr hn32 (by omega) n le_rfl, rowZero,
    readWord_mpZeroed s _ n addr hn32 (by omega),
    read_stage_outside M 2048 n addr (by rcases hfast with h | h <;> omega)]

theorem read_rowZero (s : State) (M : ByteArray) (n addr : Nat) (hn32 : n ≤ 32)
    (hfast : n = 4 ∨ n = 8) (hd : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
    MachineState.readWord (rowZero s M n) addr = MachineState.readWord M addr := by
  rw [rowZero, readWord_mpZeroed s _ n addr hn32 hd,
    read_stage_outside M 2048 n addr (by rcases hfast with h | h <;> omega)]

/-! ## The loop invariant -/

/-- What the caller guarantees at a square's entry and every round re-establishes: the
configuration words, the cached frame words, the Montgomery inverse and the operand. -/
structure Entry (s : State) (mem : ByteArray) (p a mm : Nat)
    (tl inv m0 m96 m64 m32 : UInt256) : Prop where
  s32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2))
  tlw : MachineState.readWord mem 9440 = tl
  tlv : tl = UInt256.ofNat (8224 + 32 * (p + 2))
  ml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32)
  invw : MachineState.readWord mem 9376 = inv
  m0w : MachineState.readWord mem (32 * (p + 2) - 32) = m0
  m96w : MachineState.readWord mem 96 = m96
  m64w : MachineState.readWord mem 64 = m64
  m32w : MachineState.readWord mem 32 = m32
  minv : (m0.toNat * inv.toNat + 1) % 2 ^ 256 = 0
  arep : Model.FastRepresents mem 2048 (p + 2) a
  mrep : Model.FastRepresents mem 0 (p + 2) mm
  alt : a < mm

namespace Entry

variable {s : State} {mem : ByteArray} {p a mm : Nat} {tl inv m0 m96 m64 m32 : UInt256}

theorem minv' (h : Entry s mem p a mm tl inv m0 m96 m64 m32) :
    ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
      (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0 := by
  rw [h.m0w, h.invw]; exact h.minv

/-- The row-0 caches of `CiosReadonly` / `CiosReadonlyExtra` on the staged memory. -/
theorem cache (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    CiosReadonly.ReadonlyCache (rowZero s mem (p + 2)) (p + 2) tl inv m0 :=
  ⟨h.tlv, by
    rw [read_rowZero s mem (p + 2) 9376 hn32 hfast (Or.inr (by decide)), h.invw], by
    rw [read_rowZero s mem (p + 2) (32 * (p + 2) - 32) hn32 hfast (Or.inl (by omega)), h.m0w]⟩

theorem extra (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    CiosReadonlyExtra.ExtraCache (rowZero s mem (p + 2)) m96 m64 m32 :=
  ⟨by rw [read_rowZero s mem (p + 2) 96 hn32 hfast (Or.inl (by decide)), h.m96w],
   by rw [read_rowZero s mem (p + 2) 64 hn32 hfast (Or.inl (by decide)), h.m64w],
   by rw [read_rowZero s mem (p + 2) 32 hn32 hfast (Or.inl (by decide)), h.m32w]⟩

theorem inverse (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    inverseInvariant (rowZero s mem (p + 2)) (p + 2) := by
  unfold inverseInvariant
  rw [read_rowZero s mem (p + 2) (32 * (p + 2) - 32) hn32 hfast (Or.inl (by omega)),
    read_rowZero s mem (p + 2) 9376 hn32 hfast (Or.inr (by decide))]
  exact h.minv'

theorem snapshot (s : State) (mem : ByteArray) (p : Nat)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) :
    StagedOperand.Snapshot (rowZero s mem (p + 2)) 2048 (p + 2) :=
  (snapshot_stage mem 2048 (p + 2) (by rcases hfast with h | h <;> omega)).zeroed s
    (by rcases hfast with h | h <;> omega) (by rcases hfast with h | h <;> omega)

/-- Every round re-establishes the invariant, with the operand squared. -/
theorem round (h : Entry s mem p a mm tl inv m0 m96 m64 m32) (c : Nat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hodd : mm % 2 = 1) (hmpos : 0 < mm) :
    Entry s (SquareLoopMem.sqRound s (p + 2) c mem) p (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) mm
      tl inv m0 m96 m64 m32 where
  s32 := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 9344 (by omega) hn32 hfast (by omega)]
    exact h.s32
  tlw := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 9440 (by omega) hn32 hfast (by omega)]
    exact h.tlw
  tlv := h.tlv
  ml := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 9408 (by omega) hn32 hfast (by omega)]
    exact h.ml
  invw := by
    rw [SquareLoopMem.sqRound_readWord_high s mem (p + 2) c 9376 (by omega) hn32 hfast (by omega)]
    exact h.invw
  m0w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c (32 * (p + 2) - 32) (by omega) hn32 hfast
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
    exact h.m0w
  m96w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 96 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m96w
  m64w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 64 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m64w
  m32w := by
    rw [SquareLoopMem.sqRound_readWord_outside s mem (p + 2) c 32 (by omega) hn32 hfast
      (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide)) (Or.inl (by decide))]
    exact h.m32w
  minv := h.minv
  arep := SquareLoopMem.sqRound_represents s mem p a mm c hn32 hfast h.arep h.mrep hodd h.alt h.minv'
  mrep := SquareLoopMem.sqRound_fastRepresents_outside s mem (p + 2) c 0 (p + 2) mm (by omega) hn32 hfast
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) h.mrep
  alt := Model.montMul_lt hmpos (Limbs.radix ^ (p + 2)) a a

end Entry

/-! ## The conditional subtraction inside a round -/

/-- The `CSUB` return state as a record update (definitional). -/
theorem csReturnedState_eq (s : State) (M : ByteArray) (n : Nat) (pdst ret : UInt256)
    (rest : List UInt256) :
    Csub.csReturnedState s M n n pdst ret rest =
      { s with pc := ret, stack := rest, memory := Csub.csResultMemory M n pdst.toNat } := rfl

theorem word2048_toNat : (UInt256.ofNat 2048).toNat = 2048 := by decide

/-- The CSUB of one round: from `[2048, ret]` above any stack `tail` to `ret` with the
round's memory. -/
def gasSteps_csubRound (s : State) (M : ByteArray) (p c a mm : Nat)
    (ret : UInt256) (tail : List UInt256) (tl inv m0 m96 m64 m32 : UInt256)
    (hcap : tail.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (h : Entry s M p a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (mpCsubState s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) c)
        (UInt256.ofNat 2048) ret tail)
      { s with pc := ret, stack := tail, memory := SquareLoopMem.sqRound s (p + 2) c M } :=
  (gasSteps_csubAt s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) c) (p + 2)
    ret tail hcap hrun hcode hfork hnp hact (by omega) hn32 hjump
    (by rw [read_prefix s M (p + 2) c 9408 hn32 hfast (Or.inr (by decide))]; exact h.ml)
    (by
      rw [read_prefix s M (p + 2) c 9440 hn32 hfast (Or.inr (by decide)), h.tlw]
      exact h.tlv)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p + 2) 9344 (by omega) (Or.inr (by omega)) (p + 2)
        le_rfl, read_prefix s M (p + 2) c 9344 hn32 hfast (Or.inr (by decide))]
      exact h.s32)
    (by
      rw [Csub.csStep_readWord_disjoint _ (p + 2) 8224 (by omega) (Or.inr (by omega)) (p + 2)
          le_rfl,
        readWord_countMem_disjoint _ c 8224 (Or.inl (by omega))]
      exact SquareLoopMem.tn_le_one s M p a mm hn32 hfast h.arep h.mrep h.alt h.minv')).cast rfl
    (by rw [sqRound_eq])

/-! ## One round -/

/-- A round that is **not** the last: the rows, `sq_exit`'s decrement, the CSUB subroutine
and `again`, ending at the next square's row-0 head. -/
def gasSteps_roundMore (s : State) (M : ByteArray) (p c a mm : Nat)
    (a0 tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0)
    (hcpos : 0 < c) (hc16 : c + 1 ≤ 16)
    (hcount : MachineState.readWord M 9280 = UInt256.ofNat (c + 1))
    (h : Entry s M p a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (rowState s a0 (rowZero s M (p + 2)) (p + 2) tl inv m0 m96 m64 m32
        (UInt256.ofNat 2048) ret rest 0)
      (rowState s (UInt256.ofNat 0) (rowZero s (SquareLoopMem.sqRound s (p + 2) c M) (p + 2)) (p + 2)
        tl inv m0 m96 m64 m32 (UInt256.ofNat 2048) ret rest 0) := by
  have hcountRows : MachineState.readWord
      (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) 9280 = UInt256.ofNat (c + 1) := by
    rw [readWord_sqRowsCarry _ (p + 2) 9280 hn32 (Or.inr (by omega)) (p + 2) le_rfl,
      read_rowZero s M (p + 2) 9280 hn32 hfast (Or.inr (by omega))]
    exact hcount
  have hs32' : MachineState.readWord (SquareLoopMem.sqRound s (p + 2) c M) 9344 =
      UInt256.ofNat (32 * (p + 2)) := by
    rw [SquareLoopMem.sqRound_readWord_high s M (p + 2) c 9344 (by omega) hn32 hfast (by omega)]
    exact h.s32
  have g1 := gasSteps_rowsToExit s a0 (rowZero s M (p + 2)) (p + 2) tl inv m0 m96 m64 m32
    (UInt256.ofNat 2048) ret rest (by omega) hrun hcode hfork hnp hact hfast ha0
    (h.inverse hn32 hfast) (h.cache hn32 hfast) (h.extra hn32 hfast) (Entry.snapshot s M p hfast)
  have g2 := gasSteps_sqExitMore s (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) (p + 2) c
    (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
    (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp hact hcpos hc16 hcountRows
  have g3 := gasSteps_more s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) c)
    (p + 2) (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
    (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp
  have hjumpAgain : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat pcAgain).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    exact jumpDest4762
  have g4 := gasSteps_csubRound s M p c a mm (UInt256.ofNat pcAgain)
    (frameStack (p + 2) (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
      (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
      (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest)
    tl inv m0 m96 m64 m32
    (by simp only [frameStack, List.length_append, List.length_cons, List.length_nil]; omega)
    hrun hcode hfork hnp hact hn32 hfast hjumpAgain h
  have g5 := gasSteps_again s (SquareLoopMem.sqRound s (p + 2) c M) (p + 2) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp hact hfast hcds hs32' SquareRow.jumpDest4710
  exact ((((g1.trans g2).trans g3).trans g4).trans g5)

/-- The **last** round: the rows, `sq_exit`'s decrement to zero, the `ret` rewrite, the
frame drop and the CSUB, returning to `after_sq` (3243). -/
def gasSteps_roundLast (s : State) (M : ByteArray) (p a mm : Nat)
    (a0 tl inv m0 m96 m64 m32 ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0)
    (hcount : MachineState.readWord M 9280 = UInt256.ofNat 1)
    (h : Entry s M p a mm tl inv m0 m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (rowState s a0 (rowZero s M (p + 2)) (p + 2) tl inv m0 m96 m64 m32
        (UInt256.ofNat 2048) ret rest 0)
      { s with pc := UInt256.ofNat 3231, stack := rest,
               memory := SquareLoopMem.sqRound s (p + 2) 0 M } := by
  have hcountRows : MachineState.readWord
      (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) 9280 = UInt256.ofNat 1 := by
    rw [readWord_sqRowsCarry _ (p + 2) 9280 hn32 (Or.inr (by omega)) (p + 2) le_rfl,
      read_rowZero s M (p + 2) 9280 hn32 hfast (Or.inr (by omega))]
    exact hcount
  have g1 := gasSteps_rowsToExit s a0 (rowZero s M (p + 2)) (p + 2) tl inv m0 m96 m64 m32
    (UInt256.ofNat 2048) ret rest (by omega) hrun hcode hfork hnp hact hfast ha0
    (h.inverse hn32 hfast) (h.cache hn32 hfast) (h.extra hn32 hfast) (Entry.snapshot s M p hfast)
  have g2 := gasSteps_sqExitLast s (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) (p + 2)
    (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
    (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp hact hcountRows
  have g3 := gasSteps_last s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) 0)
    (p + 2) (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
    (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp
  have g4 := gasSteps_nxExit s (countMem (sqRowsCarry (rowZero s M (p + 2)) (p + 2) (p + 2)) 0)
    (p + 2) (UInt256.ofNat (ptrAt (2048 + 32 * (p + 2) - 32) (p + 2)))
    (UInt256.ofNat (sqEnt (p + 2) (p + 2))) tl inv m0 m96 m64 m32
    (sqLast (rowZero s M (p + 2)) (p + 2)) (UInt256.ofNat 2048) (UInt256.ofNat 3231) rest
    (by omega) hrun hcode hfork hnp
  have hjumpAfter : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 3231).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
    exact jumpDest3272
  have g5 := gasSteps_csubRound s M p 0 a mm (UInt256.ofNat 3231) rest tl inv m0 m96 m64 m32
    (by omega) hrun hcode hfork hnp hact hn32 hfast hjumpAfter h
  exact ((((g1.trans g2).trans g3).trans g4).trans g5)

/-! ## The loop -/

/-- **`k` squares in one kernel call**, from the row-0 head of the first one. -/
def gasSteps_loop (s : State) (p mm : Nat) (tl inv m0 m96 m64 m32 ret : UInt256)
    (rest : List UInt256)
    (hcap : rest.length ≤ 982) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hodd : mm % 2 = 1) (hmpos : 0 < mm) :
    ∀ (k : Nat) (M : ByteArray) (a : Nat) (a0 : UInt256), 1 ≤ k → k ≤ 16 →
      UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0 →
      MachineState.readWord M 9280 = UInt256.ofNat k →
      Entry s M p a mm tl inv m0 m96 m64 m32 →
      Challenge.EvmProof.GasSteps
        (rowState s a0 (rowZero s M (p + 2)) (p + 2) tl inv m0 m96 m64 m32
          (UInt256.ofNat 2048) ret rest 0)
        { s with pc := UInt256.ofNat 3231, stack := rest,
                 memory := sqLoopMem s (p + 2) k M } := by
  intro k
  induction k with
  | zero => intro M a a0 hk; exact absurd hk (by omega)
  | succ j ih =>
      intro M a a0 _ hk16 ha0 hcount h
      match j, ih with
      | 0, _ =>
          exact gasSteps_roundLast s M p a mm a0 tl inv m0 m96 m64 m32 ret rest hcap hrun hcode
            hfork hnp hact hn32 hfast ha0 hcount h
      | (i + 1), ih =>
          exact (gasSteps_roundMore s M p (i + 1) a mm a0 tl inv m0 m96 m64 m32 ret rest hcap
            hrun hcode hfork hnp hact hn32 hfast hcds ha0 (by omega) (by omega) hcount h).trans
            (ih (SquareLoopMem.sqRound s (p + 2) (i + 1) M)
              (Model.montMul mm (Limbs.radix ^ (p + 2)) a a) (UInt256.ofNat 0)
              (by omega) (by omega) (by decide)
              (SquareLoopMem.sqRound_count s M (p + 2) (i + 1) (by omega) hn32 (by omega))
              (h.round (i + 1) hn32 hfast hodd hmpos))

/-! ## The whole call -/

theorem l1Target_eq_sqEnt (n : Nat) (hn : n = 4 ∨ n = 8) :
    CiosCached.l1Target n = UInt256.ofNat (sqEnt n 0) := by
  rcases hn with rfl | rfl <;> decide

/-- **The looped square subroutine of the sqCP1mL artifact**: entered at the kernel's
`common` block with the row head `sq_row` and the counter `k` in memory word 9280, it runs
`k` Montgomery squares of the block at 2048 and returns to `after_sq` (3243). -/
def gasSteps_squareLoop (s : State) (mem : ByteArray) (p a mm k : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 982)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hfast : p + 2 = 4 ∨ p + 2 = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hcount : MachineState.readWord mem 9280 = UInt256.ofNat k)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (ha : Model.FastRepresents mem 2048 (p + 2) a) (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.commonState s mem 4788 2048 2048 (UInt256.ofNat 2048) ret rest)
      { s with pc := UInt256.ofNat 3231, stack := rest,
               memory := sqLoopMem s (p + 2) k mem } := by
  have hentry : Entry s mem p a mm (MachineState.readWord mem 9440)
      (MachineState.readWord mem 9376) (MachineState.readWord mem (32 * (p + 2) - 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64)
      (MachineState.readWord mem 32) :=
    ⟨hs32, rfl, htl, hml, rfl, rfl, rfl, rfl, rfl, hminv, ha, hm, ham⟩
  have g1 := Cios2Dispatch.gasSteps_commonSetupInput s mem (UInt256.ofNat 4788) 2048 2048 (p + 2)
    (UInt256.ofNat 2048) ret rest (by omega) hrun hcode hfork hnp hact hfast (by omega)
    (by decide) (by omega) hcds hs32 hml Cios2Dispatch.jumpDestSqRow'
  rw [l1Target_eq_sqEnt (p + 2) hfast, rowZero_eq_input s mem (p + 2) hfast] at g1
  exact g1.trans (gasSteps_loop s p mm (MachineState.readWord mem 9440)
    (MachineState.readWord mem 9376) (MachineState.readWord mem (32 * (p + 2) - 32))
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) ret rest hcap hrun hcode hfork hnp hact hn32 hfast hcds
    hodd hmpos k mem a (UInt256.ofNat (2048 + 32 * (p + 2) - 32)) hk hk16
    (sgt_zero_setup (p + 2) (by omega)) hcount hentry)

end Challenge.Modexp.Submission.Proofs.Fast.SquareLoop

import Challenge.Modexp.Submission.Proofs.Fast.SquareRows
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# `SQUARE(2048) → 2048` through the sqCP1m kernel

The fixed-exponent caller enters the kernel's `common` block (pc 3924) with the row
head `hd = sq_row = 4710` on top of the call frame `[2048, 2048, 2048, ret]`
(`Cios2Dispatch.commonState s mem 4710 2048 2048 (ofNat 2048) ret rest`, definitionally
`Exp.sqCall`).

* `n ∈ {4, 8}`: the call does **not** return to `ret` on the R0 artifact — the kernel keeps
  its frame, loops over the counter in memory word 9280 and leaves through `after_sq`
  (3243).  That path is `SquareLoop.gasSteps_squareLoop`; this lemma therefore carries
  `hslow : ¬(n = 4 ∨ n = 8)`.
* other widths: `common` falls back (`POP PUSH2 0x683 JUMP`) to the generic `MONPRO`
  at 1667 (`Cios2Dispatch.gasSteps_commonFallbackOfWidth`, `Monpro.gasSteps_monproCsub`),
  which returns to `ret` with memory `SquareResult.sqMem s mem n`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult SquareRow SquareRows
open CiosCachedMidMemory CarryRowModel StagedOperand

/-- The setup's first-loop entry is the square row 0 entry. -/
theorem l1Target_eq_sqEnt (n : Nat) (hn : n = 4 ∨ n = 8) :
    CiosCached.l1Target n = UInt256.ofNat (sqEnt n 0) := by
  rcases hn with rfl | rfl <;> decide

/-- The `CSUB` return state as a record update (definitional). -/
theorem csReturnedState_eq (s : State) (M : ByteArray) (n : Nat) (pdst ret : UInt256)
    (rest : List UInt256) :
    Csub.csReturnedState s M n n pdst ret rest =
      { s with pc := ret, stack := rest, memory := Csub.csResultMemory M n pdst.toNat } := rfl

theorem word2048_toNat : (UInt256.ofNat 2048).toNat = 2048 := by decide

/-- **The square subroutine** `SQUARE(2048) → 2048` of the sqCP1m artifact: from the
`common` entry with row head `sq_row` to the caller's return address, leaving
`SquareResult.sqMem s mem (p + 2)` in memory. -/
def gasSteps_squareFull (s : State) (mem : ByteArray) (p a mm : Nat)
    (ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hslow : ¬(p + 2 = 4 ∨ p + 2 = 8))
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (ha : Model.FastRepresents mem 2048 (p + 2) a) (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.commonState s mem 4923 2048 2048 (UInt256.ofNat 2048) ret rest)
      { s with pc := ret, stack := rest, memory := SquareResult.sqMem s mem (p + 2) } := by
  -- the generic MONPRO fallback (the kernel path is `SquareLoop.gasSteps_squareLoop`)
  have g1 := Cios2Dispatch.gasSteps_commonFallbackOfWidth s mem 4923 2048 2048 (p + 2)
    (UInt256.ofNat 2048) ret rest (by omega) hrun hcode hfork hnp hact hn32 hs32
    (fun h => hslow (Or.inl h)) (fun h => hslow (Or.inr h))
  have g2 := Monpro.gasSteps_monproCsub s mem 2048 2048 (p + 2) (UInt256.ofNat 2048) ret rest
    (by omega) hrun hcode hfork hnp hact (by omega) hn32 (by decide) (by omega) (by decide)
    (by omega) hcds hs32 htl hml hjump
    (by rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; omega)
    (Monpro.monpro_tn_le_one s mem 2048 2048 p a a mm hn32 (by omega) (by omega) ha ha hm ham
      hmpos hminv)
  refine (g1.trans g2).cast rfl ?_
  rw [csReturnedState_eq, sqMem_of_not_fast s mem (p + 2) hslow, Monpro.monproMem_def,
    word2048_toNat]

end Challenge.Modexp.Submission.Proofs.Fast.SquareFull

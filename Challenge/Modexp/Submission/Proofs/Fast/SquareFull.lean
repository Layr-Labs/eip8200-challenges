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
WP-C's `Exp.sqCall`).

* `n ∈ {4, 8}`: the width check passes and the 3-slot `setup` stages the operand and
  zeroes the accumulator (`Cios2Dispatch.gasSteps_commonSetupInput`, row-0 memory
  `M0 = mpZeroed s (inputMemory mem 2048 n) n`); the `n` square rows run
  (`SquareRows.gasSteps_rows`); the kernel exit jumps to the final conditional
  subtraction (`Csub.gasSteps_csub`, side condition `t[n] ≤ 1` =
  `SquareResult.sqRowsCarry_tn_le_one`), which returns to `ret`.
* other widths: `common` falls back (`POP PUSH2 0x683 JUMP`) to the generic `MONPRO`
  at 1667 (`Cios2Dispatch.gasSteps_commonFallbackOfWidth`, `Monpro.gasSteps_monproCsub`).

Either way the caller gets back memory `SquareResult.sqMem s mem n`.
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
      (Cios2Dispatch.commonState s mem 4714 2048 2048 (UInt256.ofNat 2048) ret rest)
      { s with pc := ret, stack := rest, memory := SquareResult.sqMem s mem (p + 2) } := by
  by_cases hfast : p + 2 = 4 ∨ p + 2 = 8
  · -- the square kernel
    have hn8 : p + 2 ≤ 8 := by omega
    have hread (addr : Nat) (hd : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
        MachineState.readWord (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) addr =
          MachineState.readWord mem addr :=
      (readWord_mpZeroed s _ (p + 2) addr hn32 hd).trans
        (read_inputMemory_outside mem 2048 (p + 2) addr hd)
    -- setup: row head 0 of the square rows
    have g1 := Cios2Dispatch.gasSteps_commonSetupInput s mem (UInt256.ofNat 4714) 2048 2048 (p + 2)
      (UInt256.ofNat 2048) ret rest hcap hrun hcode hfork hnp hact hfast (by omega) (by decide)
      (by omega) hcds hs32 hml Cios2Dispatch.jumpDestSqRow'
    rw [l1Target_eq_sqEnt (p + 2) hfast] at g1
    -- the rows
    have hcM : CiosReadonly.ReadonlyCache (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) (p + 2)
        (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
        (MachineState.readWord mem (32 * (p + 2) - 32)) :=
      ⟨htl, (hread 9376 (Or.inr (by decide))).symm, (hread (32 * (p + 2) - 32) (Or.inl (by omega))).symm⟩
    have heM : CiosReadonlyExtra.ExtraCache (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2))
        (MachineState.readWord mem 96) (MachineState.readWord mem 64) (MachineState.readWord mem 32) :=
      ⟨(hread 96 (Or.inl (by decide))).symm, (hread 64 (Or.inl (by decide))).symm,
        (hread 32 (Or.inl (by decide))).symm⟩
    have hminvM : inverseInvariant (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) (p + 2) := by
      unfold inverseInvariant
      rw [hread (32 * (p + 2) - 32) (Or.inl (by omega)), hread 9376 (Or.inr (by decide))]
      exact hminv
    have hin : inputMemory mem 2048 (p + 2) = stage mem 2048 (p + 2) := by
      unfold inputMemory; rw [if_pos hfast]
    have hsnapM : StagedOperand.Snapshot (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) 2048 (p + 2) := by
      rw [hin]; exact (snapshot_stage mem 2048 (p + 2) (by omega)).zeroed s hn8 (by omega)
    have g2 := gasSteps_rows s (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) (p + 2)
      (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
      (MachineState.readWord mem (32 * (p + 2) - 32))
      (MachineState.readWord mem 96) (MachineState.readWord mem 64) (MachineState.readWord mem 32)
      (UInt256.ofNat 2048) ret rest hcap hrun hcode hfork hnp hact hfast hminvM hcM heM hsnapM
    -- the final conditional subtraction
    have hrowsRead (addr : Nat) (hd : addr + 32 ≤ 8192 ∨ 9280 ≤ addr) :
        MachineState.readWord (sqRowsCarry (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) (p + 2) (p + 2))
          addr = MachineState.readWord mem addr :=
      (readWord_sqRowsCarry _ (p + 2) addr hn32 hd (p + 2) le_rfl).trans (hread addr hd)
    have htn : (MachineState.readWord (Csub.csStep (sqRowsCarry (mpZeroed s (inputMemory mem 2048 (p + 2))
        (p + 2)) (p + 2) (p + 2)) (p + 2) (p + 2)).memory 8224).toNat ≤ 1 := by
      rw [Csub.csStep_readWord_disjoint _ (p + 2) 8224 (by omega) (Or.inr (by omega)) (p + 2) le_rfl]
      have ha0 : Model.FastRepresents (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) 2048 (p + 2) a := by
        refine (Model.fastRepresents_congr (a := mem) ?_ a).1 ha
        intro j hj
        rw [hread (2048 + 32 * j) (Or.inl (by omega))]
      have hm0 : Model.FastRepresents (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) 0 (p + 2) mm := by
        refine (Model.fastRepresents_congr (a := mem) ?_ mm).1 hm
        intro j hj
        rw [hread (0 + 32 * j) (Or.inl (by omega))]
      have hminv0 : ((MachineState.readWord (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2))
          (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) 9376).toNat + 1) %
            2 ^ 256 = 0 := by
        rw [hread (32 * (p + 2) - 32) (Or.inl (by omega)), hread 9376 (Or.inr (by decide))]
        exact hminv
      exact sqRowsCarry_tn_le_one _ p a mm hn32 ha0 hm0 hminv0 (tValue_mpZeroed s _ (p + 2)) ham
    have g3 := Csub.gasSteps_csub s
      (sqRowsCarry (mpZeroed s (inputMemory mem 2048 (p + 2)) (p + 2)) (p + 2) (p + 2)) (p + 2)
      (UInt256.ofNat 2048) ret rest (by omega) hcode hfork hrun hnp hact (by omega) hn32 hjump
      ((hrowsRead 9408 (Or.inr (by decide))).trans hml)
      ((hrowsRead 9440 (Or.inr (by decide))).trans htl)
      ((Csub.csStep_readWord_disjoint _ (p + 2) 9344 (by omega) (Or.inr (by omega)) (p + 2) le_rfl).trans
        ((hrowsRead 9344 (Or.inr (by decide))).trans hs32))
      (by rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; omega)
      htn
    refine (g1.trans (g2.trans g3)).cast rfl ?_
    rw [csReturnedState_eq, sqMem_of_fast s mem (p + 2) hfast, word2048_toNat]
  · -- the generic MONPRO fallback
    have g1 := Cios2Dispatch.gasSteps_commonFallbackOfWidth s mem 4714 2048 2048 (p + 2)
      (UInt256.ofNat 2048) ret rest (by omega) hrun hcode hfork hnp hact hn32 hs32
      (fun h => hfast (Or.inl h)) (fun h => hfast (Or.inr h))
    have g2 := Monpro.gasSteps_monproCsub s mem 2048 2048 (p + 2) (UInt256.ofNat 2048) ret rest
      (by omega) hrun hcode hfork hnp hact (by omega) hn32 (by decide) (by omega) (by decide)
      (by omega) hcds hs32 htl hml hjump
      (by rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]; omega)
      (Monpro.monpro_tn_le_one s mem 2048 2048 p a a mm hn32 (by omega) (by omega) ha ha hm ham
        hmpos hminv)
    refine (g1.trans g2).cast rfl ?_
    rw [csReturnedState_eq, sqMem_of_not_fast s mem (p + 2) hfast, Monpro.monproMem_def,
      word2048_toNat]

end Challenge.Modexp.Submission.Proofs.Fast.SquareFull

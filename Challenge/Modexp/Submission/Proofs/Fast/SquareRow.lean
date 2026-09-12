import Challenge.Modexp.Submission.Proofs.Fast.SquareRowRun

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel
/-! ## The prologue on the kernel row frame -/

/-- The row pointer of square row `i` is the address of `a_i`. -/
theorem ptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    (UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)).toNat = aAddr n i := by
  rw [ptrAt_toNat _ _ (by omega) (by omega), aAddr]
  omega

/-- ... and `P + 0x1840` is the address of `t_i`. -/
theorem tptr_toNat (n i : Nat) (hi : i < n) (hn : n ≤ 32) :
    ((1600 : UInt256) + UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)).toNat = tAddr n i := by
  rw [Challenge.EvmProof.Word.word_toNat_add, ptr_toNat n i hi hn, aAddr, tAddr]
  have h6208 : (1600 : UInt256).toNat = 1600 := rfl
  rw [h6208, Nat.mod_eq_of_lt (by omega)]
  omega

theorem push0_eq : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := by decide

/-- **The `sq_row` prologue of square row `i`** (`i < n ≤ 8`, operand at 512): from the
row head (`hd = 4710`, frame slot `ent = e`, slot 14 = `aprev`) to the first-loop entry
`e` with memory/carry `SquareModel.sqPro mem n i tb` (`tb = SGT 0 aprev`), multiplier
`b2 = sqB2 x tb`, frame slot `ent := e + 38` and slot 14 := `x = a_i`. -/
def gasSteps_prologue (s : State) (mem : ByteArray) (n i e : Nat)
    (pdst ret w10 w11 w12 w13 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode e = true)
    (he : e + 38 < 2 ^ 256) :
    Challenge.EvmProof.GasSteps
      (outState s mem 512 n i (UInt256.ofNat 4710) (UInt256.ofNat e) pdst ret
        (w10 :: w11 :: w12 :: w13 :: aprev :: rest))
      (l1Q e s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev))
        (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 512 n i
        (UInt256.ofNat 4710) (UInt256.ofNat (e + 38)) pdst ret
        (w10 :: w11 :: w12 :: w13 :: sqX mem n i :: rest)) := by
  let P : UInt256 := UInt256.ofNat (ptrAt (512 + 32 * n - 32) i)
  let s' : State := { s with memory := mem }
  have hP : P.toNat = aAddr n i := ptr_toNat n i hi (by omega)
  have hT : ((1600 : UInt256) + P).toNat = tAddr n i := tptr_toNat n i hi (by omega)
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat P.toNat 32) =
      s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat
      ((1600 : UInt256) + P).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  have hjumpE : Decode.isValidJumpDest s'.executionEnv.code (UInt256.ofNat e).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change Decode.isValidJumpDest s.executionEnv.code e = true
    rw [hcode]; exact hjump
  -- block A
  have hA := run_A s' P (UInt256.ofNat 4710) (UInt256.ofNat (512 - 32)) (UInt256.ofNat e)
    negative32 allOnes (l2Target n) pdst ret w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [push0_eq] at hA
  have gA := stepsOf blockA hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := SgtStep.gasSteps_sqRowSgt
    { s' with pc := UInt256.ofNat 4716,
              stack := UInt256.ofNat 0 :: aprev :: MachineState.readWord s'.memory P.toNat :: P ::
                UInt256.ofNat 4710 :: UInt256.ofNat (512 - 32) :: UInt256.ofNat e :: negative32 ::
                allOnes :: l2Target n :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
                MachineState.readWord s'.memory P.toNat :: rest }
    (UInt256.ofNat 0) aprev _ hcode hfork rfl rfl (by simp only [List.length_cons]; omega) hrun hnp
  -- block B
  have hB := run_B s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory P.toNat) P
    (UInt256.ofNat 4710) (UInt256.ofNat (512 - 32)) (UInt256.ofNat e) negative32 allOnes
    (l2Target n :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
      MachineState.readWord s'.memory P.toNat :: rest)
    (by simp only [List.length_cons]; omega) hactT hjumpE
  have gB := stepsOf blockB hB rfl hcode hfork hrun hnp
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, outState,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.SquareRow

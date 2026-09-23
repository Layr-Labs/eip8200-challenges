import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareBlocks
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.TnM128ReductionSteps
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL1Trace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSteps
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore SquareModel
open TnCacheSquareTrace TnM128SquareBlocks

def outState (tn m128 : UInt256) (s : State) (mem : ByteArray) (pb n i : Nat)
    (hd ent inv m0 : UInt256) (rest : List UInt256) : State :=
  framed {s with memory := mem} hd
    (TnCacheFrameOps.frame (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
      (UInt256.ofNat (pb-32)) ent tn m128 inv
      (m0 :: rest))

def l1Q (tn m128 : UInt256) (pc : Nat) (s : State) (q : MacState) (bi : UInt256) (pb n i : Nat)
    (hd ent inv m0 : UInt256) (rest : List UInt256) : State :=
  TnCacheL1Trace.qState s (UInt256.ofNat pc) q bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd (UInt256.ofNat (pb-32)) ent tn
    m128 inv (m0 :: rest)

def environment (s : State) (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment TnM128CandidateArtifact.submissionArtifact .Osaka s :=
  ⟨by change TnM128Candidate.bytecode.size < 2^256; rw [TnM128Candidate.bytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

def stepsOf {pc : Nat} {instructions : List Instr}
    (block : Block TnM128CandidateArtifact.submissionArtifact .Osaka pc instructions) {s t : State}
    (hrun' : runInstructions instructions s = some t) (hpc : s.pc = UInt256.ofNat pc)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  block.steps (environment s hcode hfork hrun hnp) hpc hrun'

noncomputable def prologue_steps (s : State) (mem : ByteArray) (tn m128 : UInt256) (n i e : Nat)
    (pdst ret w10 w11 w12 w13 aprev : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < n) (hn : n ≤ 8)
    (hjump : Decode.isValidJumpDest TnM128Candidate.bytecode e = true)
    (he : e + 37 < 2 ^ 256) :
    Challenge.EvmProof.GasSteps
      (outState tn m128 s mem 2368 n i (UInt256.ofNat 4258) (UInt256.ofNat e) pdst ret
        (w10 :: w11 :: w12 :: w13 :: aprev :: rest))
      (l1Q tn m128 e s (sqPro mem n i (UInt256.sgt (UInt256.ofNat 0) aprev))
        (sqB2 (sqX mem n i) (UInt256.sgt (UInt256.ofNat 0) aprev)) 2368 n i
        (UInt256.ofNat 4258) (UInt256.ofNat (e + 37)) pdst ret
        (w10 :: w11 :: w12 :: w13 :: sqX mem n i :: rest)) := by
  let P : UInt256 := UInt256.ofNat (ptrAt (2368 + 32 * n - 32) i)
  let s' : State := { s with memory := mem }
  have hP : P.toNat = aAddr n i := ptr_toNat n i hi (by omega)
  have hT : (P - (256 : UInt256)).toNat = tAddr n i := tptr_toNat n i hi (by omega)
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat P.toNat 32) =
      s'.activeWords := by
    rw [hP]; exact activeWords_fix s' _ 32 (by decide) (by rw [aAddr]; omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s'.activeWords.toNat
      (P - (256 : UInt256)).toNat 32) = s'.activeWords := by
    rw [hT]; exact activeWords_fix s' _ 32 (by decide) (by rw [tAddr]; omega) hact
  have hjumpE : Decode.isValidJumpDest s'.executionEnv.code (UInt256.ofNat e).toNat = true := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change Decode.isValidJumpDest s.executionEnv.code e = true
    rw [hcode]; exact hjump
  -- block A
  have hA := run_A s' P (UInt256.ofNat 4258) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e)
    tn allOnes m128 pdst ret w10 w11 w12 w13 aprev rest (by omega) hactP
  rw [push0_eq] at hA
  have gA := stepsOf blockA hA rfl hcode hfork hrun hnp
  -- the SGT
  have gS := TnM128SgtStep.gasSteps_sqRowSgt
    { s' with pc := UInt256.ofNat 4264,
              stack := UInt256.ofNat 0 :: aprev :: MachineState.readWord s'.memory P.toNat :: P ::
                UInt256.ofNat 4258 :: UInt256.ofNat (2368 - 32) :: UInt256.ofNat e :: tn ::
                allOnes :: m128 :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
                MachineState.readWord s'.memory P.toNat :: rest }
    (UInt256.ofNat 0) aprev _ hcode hfork rfl rfl (by simp only [List.length_cons]; omega) hrun hnp
  -- block B
  have hB := run_B s' (UInt256.sgt (UInt256.ofNat 0) aprev) (MachineState.readWord s'.memory P.toNat) P
    (UInt256.ofNat 4258) (UInt256.ofNat (2368 - 32)) (UInt256.ofNat e) tn allOnes
    (m128 :: pdst :: ret :: w10 :: w11 :: w12 :: w13 ::
      MachineState.readWord s'.memory P.toNat :: rest)
    (by simp only [List.length_cons]; omega) hactT hjumpE
  have gB := stepsOf blockB hB rfl hcode hfork hrun hnp
  refine (gA.trans gS).trans (gB.cast rfl ?_)
  simp only [s', hP, hT, l1Q, sqPro_eq, sqB2, sqX, outState,
    TnCacheL1Trace.qState, TnCacheFrameOps.frame, CiosCachedMacCore.framed,
    Challenge.EvmProof.Word.ofNat_add_mod, List.cons_append, List.nil_append]
  rfl

#print axioms prologue_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSteps

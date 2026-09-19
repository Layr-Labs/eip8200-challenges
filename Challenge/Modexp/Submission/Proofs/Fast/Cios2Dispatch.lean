import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnM128PreclearEntry
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareSetup
import Challenge.Modexp.Submission.Proofs.Fast.SquarePreclearMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
Kernel dispatch and setup for the D2 artifact.  The generic entry at 5454 clears the
scratch region before entering the legacy two-instruction multiply entry at 3390.
The common entry at 3394 is the partial-clear square setup.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel WindowTwentyOneBinding

/-- The generic multiply call state at pc 5454. -/
def dispatchState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5454
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The state after the preclear jump, at the legacy two-instruction entry. -/
abbrev legacyState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  TnM128PreclearEntry.legacyState s mem pa pb pdst ret rest

/-- The shared partial-clear square setup at pc 3394. -/
def commonState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3394
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

theorem jumpDestPreclear :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5454 = true := by
  exact TnM128PreclearEntry.jumpDest

theorem jumpDest4012 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3390 = true := by
  exact Artifact.isValidJumpDest_index 2711 (by rfl)

theorem jumpDestCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3394 = true := by
  exact Artifact.isValidJumpDest_index 2713 (by rfl)

theorem jumpDestRowHead :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3543 = true := by
  exact Artifact.isValidJumpDest_index 2815 (by rfl)

theorem jumpDestSqRow :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4268 = true := by
  exact Artifact.isValidJumpDest_index 3387 (by rfl)

theorem jumpDestRowHead' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 3543).toNat = true := by
  rw [show (UInt256.ofNat 3543).toNat = 3543 by decide]
  exact jumpDestRowHead

theorem jumpDestSqRow' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4268).toNat = true := by
  rw [show (UInt256.ofNat 4268).toNat = 4268 by decide]
  exact jumpDestSqRow

example (s : State) (mem : ByteArray) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3394
              stack := UInt256.ofNat 4268 :: UInt256.ofNat 512 :: UInt256.ofNat 512 ::
                UInt256.ofNat 512 :: ret :: tail
              memory := mem } : State) =
      commonState s mem 4268 512 512 (UInt256.ofNat 512) ret tail := rfl

example (s : State) (mem : ByteArray) (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 5454
              stack := UInt256.ofNat pa :: UInt256.ofNat pb :: UInt256.ofNat pd :: ret :: tail
              memory := mem } : State) =
      dispatchState s mem pa pb (UInt256.ofNat pd) ret tail := rfl

theorem run_mulEntry (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions mulEntryProgram (legacyState s mem pa pb pdst ret rest) =
      some (commonState s mem (UInt256.ofNat 3543) pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [mulEntryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    legacyState, TnM128PreclearEntry.legacyState, commonState, hc4,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

/-- `common` falls through to the setup entry. -/
theorem run_commonGuard (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (_hact : 88 ≤ s.activeWords.toNat)
    (_hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 128 ∨
      MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (_hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (_hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    runInstructions commonGuardProgram (commonState s mem hd pa pb pdst ret rest) =
      some (CiosCached.setupState s mem hd pa pb pdst ret rest) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [commonGuardProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    commonState, CiosCached.setupState, hc5, Challenge.EvmProof.Word.succ_ofNat_mod]

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by
    change Challenge.Modexp.submissionBytecode.size < 2^256
    rw [Challenge.Modexp.submissionBytecode_size]
    decide,
    hcode, hfork, hrun, hnp⟩

/-- Generic entry preclear, followed by the legacy two-instruction entry. -/
opaque gasSteps_mulEntry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (commonState s (mpZeroed s mem n) (UInt256.ofNat 3543) pa pb pdst ret rest) := by
  refine (TnM128PreclearEntry.gasSteps_entry s mem pa pb n pdst ret rest
    hcap hrun hcode hfork hnp hact hn hcds hs32).trans ?_
  exact mulEntry.steps
    (environment (legacyState s (mpZeroed s mem n) pa pb pdst ret rest)
      hcode hfork hrun hnp)
    rfl (run_mulEntry s (mpZeroed s mem n) pa pb pdst ret rest hcap)

/-- The common one-instruction prefix, on an already precleared memory. -/
opaque gasSteps_common (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 128 ∨
      MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.setupState s mem hd pa pb pdst ret rest) :=
  commonGuard.steps
    (environment (commonState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (run_commonGuard s mem hd pa pb pdst ret rest hcap hcode hact hs32 hguard hzero)

opaque gasSteps_dispatch4 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 128)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.setupState s (mpZeroed s mem 4) (UInt256.ofNat 3543)
        pa pb pdst ret rest) := by
  have hs32' : MachineState.readWord (mpZeroed s mem 4) 2688 = UInt256.ofNat 128 := by
    rw [StagedMonpro.readWord_mpZeroed s mem 4 2688 (by decide) (Or.inr (by decide))]
    exact hs32
  have hguard' : MachineState.readWord (mpZeroed s mem 4) 2720 ≠ UInt256.ofNat 1 := by
    simpa only [StagedMonpro.readWord_mpZeroed s mem 4 2720 (by decide) (Or.inr (by decide))]
      using hguard
  have hzero' : MachineState.readWord (mpZeroed s mem 4) 2720 ≠ UInt256.ofNat 0 := by
    simpa only [StagedMonpro.readWord_mpZeroed s mem 4 2720 (by decide) (Or.inr (by decide))]
      using hzero
  refine (gasSteps_mulEntry s mem pa pb 4 pdst ret rest hcap hrun hcode hfork hnp
    hact (by decide) hcds hs32).trans ?_
  exact gasSteps_common s (mpZeroed s mem 4) (UInt256.ofNat 3543) pa pb pdst ret rest
    hcap hrun hcode hfork hnp hact (Or.inl hs32') hguard' hzero'

opaque gasSteps_dispatch8 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.setupState s (mpZeroed s mem 8) (UInt256.ofNat 3543)
        pa pb pdst ret rest) := by
  have hs32' : MachineState.readWord (mpZeroed s mem 8) 2688 = UInt256.ofNat 256 := by
    rw [StagedMonpro.readWord_mpZeroed s mem 8 2688 (by decide) (Or.inr (by decide))]
    exact hs32
  have hguard' : MachineState.readWord (mpZeroed s mem 8) 2720 ≠ UInt256.ofNat 1 := by
    simpa only [StagedMonpro.readWord_mpZeroed s mem 8 2720 (by decide) (Or.inr (by decide))]
      using hguard
  have hzero' : MachineState.readWord (mpZeroed s mem 8) 2720 ≠ UInt256.ofNat 0 := by
    simpa only [StagedMonpro.readWord_mpZeroed s mem 8 2720 (by decide) (Or.inr (by decide))]
      using hzero
  refine (gasSteps_mulEntry s mem pa pb 8 pdst ret rest hcap hrun hcode hfork hnp
    hact (by decide) hcds hs32).trans ?_
  exact gasSteps_common s (mpZeroed s mem 8) (UInt256.ofNat 3543) pa pb pdst ret rest
    hcap hrun hcode hfork hnp hact (Or.inr hs32') hguard' hzero'

opaque gasSteps_commonSetup (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32*n ≤ 2816)
    (hpaOutside : pa + 32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (_hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (_hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s (mpZeroed s mem n) hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n)
        pb n 0 hd (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: pdst :: ret :: rest)) := by
  have hn8 : n ≤ 8 := by omega
  have hread (addr : Nat) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
      MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr :=
    StagedMonpro.readWord_mpZeroed s mem n addr hn8 haddr
  have hs32' : MachineState.readWord (mpZeroed s mem n) 2688 = UInt256.ofNat (32*n) := by
    rw [hread 2688 (Or.inr (by omega))]
    exact hs32
  have hml' : MachineState.readWord (mpZeroed s mem n) 2752 = UInt256.ofNat (32*n-32) := by
    rw [hread 2752 (Or.inr (by omega))]
    exact hml
  have hstage := SquarePreclearMemory.partial_stage_preclear_eq s mem pa n hn8 hpaOutside
  have hentry := TnM128SquareSetup.gasSteps_entry s (mpZeroed s mem n) hd pa pb n
    pdst ret rest hcap hrun hcode hfork hnp hact hn hpaFit hpb hpbFit hs32' hml' hhd
  rw [hstage] at hentry
  simpa only [TnM128SquareSetup.input, commonState, CiosCached.outState,
    TnM128Setup.outState, TnM128Setup.l1Target, CiosCached.l1Target, TnM128Setup.zeroTn,
    hread 2720 (Or.inr (by omega)),
    hread (32*n-32) (Or.inl (by omega)),
    hread 2784 (Or.inr (by omega)),
    hread 96 (Or.inl (by decide)),
    hread 64 (Or.inl (by decide)),
    hread 32 (Or.inl (by decide))] using hentry

opaque gasSteps_commonSetupInput (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32*n ≤ 2816)
    (hpaOutside : pa + 32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32*n ≤ 2816)
    (_hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (_hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s (mpZeroed s mem n) hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.inputMemory mem pa n) n)
        pb n 0 hd (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: pdst :: ret :: rest)) := by
  have hin : StagedOperand.inputMemory mem pa n = StagedOperand.stage mem pa n := by
    unfold StagedOperand.inputMemory
    rw [if_pos (show StagedOperand.eligible mem n from ⟨hn, hguard⟩)]
  rw [hin]
  exact gasSteps_commonSetup s mem hd pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
    hpaFit hpaOutside hpb hpbFit _hcds hs32 hml hhd hguard _hzero

opaque gasSteps_mulSetup (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32*n ≤ 2816)
    (hpaOutside : pa + 32*n ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n)
        pb n 0 (UInt256.ofNat 3543) (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: pdst :: ret :: rest)) := by
  refine (gasSteps_mulEntry s mem pa pb n pdst ret rest (by omega) hrun hcode hfork hnp
    hact hn hcds hs32).trans ?_
  exact gasSteps_commonSetup s mem (UInt256.ofNat 3543) pa pb n pdst ret rest hcap hrun hcode
    hfork hnp hact hn hpaFit hpaOutside hpb hpbFit hcds hs32 hml jumpDestRowHead' hguard hzero

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

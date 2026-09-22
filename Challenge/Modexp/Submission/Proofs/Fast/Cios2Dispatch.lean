import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SetupEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
Kernel dispatch and setup, bound to the submitted cached-carry/modulus artifact.
The multiply entry at 3209 pushes row head 3358, then enters common3213 and
setup3214. The square caller selects staged-square entry4394 instead.
`TnM128Setup.run_entry` proves the 58 setup instructions, including operand
staging, zero carry initialization, and the cached modulus word at offset128.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel WindowTwentyOneBinding

/-- The multiply call state: `mul entry`, pc 4013, `[pa, pb, pdst, ret] ++ rest`. -/
def dispatchState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3383
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The shared `common` block, pc 4132, with the row head `hd` above the call frame
(`hd = 4289` after the `mul entry`, `hd = 2464` for the square). -/
def commonState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3387
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }


/-- The `mul entry` JUMPDEST (instruction 3190, pc 4013 = 0x0f50). -/
theorem jumpDest4012 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3383 = true := by
  exact Artifact.isValidJumpDest_index 2718 (by rfl)

/-- The `common` JUMPDEST (instruction 3190, pc 4132 = 0x0f54). -/
theorem jumpDestCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3387 = true := by
  exact Artifact.isValidJumpDest_index 2720 (by rfl)

/-- The multiply row head (instruction 2703, pc 3543). -/
theorem jumpDestRowHead :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3533 = true := by
  exact Artifact.isValidJumpDest_index 2821 (by rfl)

/-- The square row head `sq_row` (instruction 3275, pc 4268). -/
theorem jumpDestSqRow :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4258 = true := by
  exact Artifact.isValidJumpDest_index 3393 (by rfl)

/-- `jumpDestRowHead` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestRowHead' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 3533).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact jumpDestRowHead

/-- `jumpDestSqRow` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestSqRow' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4258).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact jumpDestSqRow

/-- The square call state (`Exp.sqCall s mem ret tail`) is definitionally `commonState`
with `hd = 2464` and `pa = pb = pdst = 2048`. -/
example (s : State) (mem : ByteArray) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3387
              stack := UInt256.ofNat 4258 :: UInt256.ofNat 512 :: UInt256.ofNat 512 ::
                UInt256.ofNat 512 :: ret :: tail
              memory := mem } : State) =
      commonState s mem 4258 512 512 (UInt256.ofNat 512) ret tail := rfl

/-- The multiply call state (`Exp.mpCall s mem pa pb pd ret tail`) is definitionally
`dispatchState`. -/
example (s : State) (mem : ByteArray) (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3383
              stack := UInt256.ofNat pa :: UInt256.ofNat pb :: UInt256.ofNat pd :: ret :: tail
              memory := mem } : State) =
      dispatchState s mem pa pb (UInt256.ofNat pd) ret tail := rfl

private theorem activeWords9344 (s : State) (hact : 88 ≤ s.activeWords.toNat) :
    UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2688 32) =
      s.activeWords := by
  have hnat : MachineState.activeWordsAfter s.activeWords.toNat 2688 32 =
      s.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    simp only [show (32 : Nat) ≠ 0 by decide, if_false]
    exact Nat.max_eq_left (by omega)
  rw [hnat]
  exact (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

private theorem toNat_ne_of_ne {a b : UInt256} (h : a ≠ b) :
    a.toNat ≠ b.toNat := by
  intro hab
  apply h
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UInt256.toNat] at hab
      congr
      exact Fin.ext hab

theorem run_mulEntry (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008) :
    runInstructions mulEntryProgram (dispatchState s mem pa pb pdst ret rest) =
      some (commonState s mem (UInt256.ofNat 3533) pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [mulEntryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    dispatchState, commonState, hc4,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
/-- `common` with a four- or eight-limb width word jumps to the kernel `setup`. -/
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

set_option linter.unusedSimpArgs false in


/-- The kernel `setup`: instructions 2602..2660 (pc 3445..3531), 59 instructions. -/
def setup : Block Artifact.submissionArtifact .Osaka 3388 TnM128Setup.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2721 58 3388 TnM128Setup.fullEntryProgram
    (by decide) (by decide) (by rfl) (by decide)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `mul entry` → `common` with `hd = 4289`. -/
opaque gasSteps_mulEntry (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (commonState s mem (UInt256.ofNat 3533) pa pb pdst ret rest) :=
  mulEntry.steps (environment _ hcode hfork hrun hnp) rfl
    (run_mulEntry s mem pa pb pdst ret rest hcap)

/-- `common` → kernel `setup` for a four- or eight-limb width (any `hd`). -/
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
  commonGuard.steps (environment (commonState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (run_commonGuard s mem hd pa pb pdst ret rest hcap hcode hact hs32 hguard hzero)


/-- Multiply, four limbs: `mul entry` → `common` → `setup` with `hd = 4289`. -/
opaque gasSteps_dispatch4 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 128)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.setupState s mem (UInt256.ofNat 3533) pa pb pdst ret rest) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest hcap hrun hcode hfork hnp).trans
    (gasSteps_common s mem (UInt256.ofNat 3533) pa pb pdst ret rest hcap hrun hcode hfork hnp
      hact (Or.inl hs32) hguard hzero)

/-- Multiply, eight limbs: `mul entry` → `common` → `setup` with `hd = 4289`. -/
opaque gasSteps_dispatch8 (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.setupState s mem (UInt256.ofNat 3533) pa pb pdst ret rest) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest hcap hrun hcode hfork hnp).trans
    (gasSteps_common s mem (UInt256.ofNat 3533) pa pb pdst ret rest hcap hrun hcode hfork hnp
      hact (Or.inr hs32) hguard hzero)


/-- The kernel `setup` (pc 4151 → `hd`): stages `a` at 2368, zeroes `t` and builds the
row-0 frame `[pbi, hd, pb-32, l1Target n, …, inv, m0, tl, m96, m64, m32, aEnd, pdst, ret]`. -/
opaque gasSteps_setup (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hn4 : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslot : rest[2]? = some (MachineState.readWord mem 2688))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true) :
    Challenge.EvmProof.GasSteps
      (CiosCached.setupState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0 hd
        (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) :=
  setup.steps (environment (CiosCached.setupState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp)
    rfl
    (TnM128Setup.run_entry s mem hd pa pb n pdst ret rest hcap hact hn hn32 hn4 hpaFit hpb hpbFit
      hcds hs32 hml hslot (by rw [hcode]; exact hjump))

/-- `common` → `setup` → row-0 head at `hd` for a four- or eight-limb width (any `hd`;
4289 for the multiply, 2464 for the square). -/
opaque gasSteps_commonSetup (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslot : rest[2]? = some (MachineState.readWord mem 2688))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0 hd
        (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) := by
  have hwidth : MachineState.readWord mem 2688 = UInt256.ofNat 128 ∨
      MachineState.readWord mem 2688 = UInt256.ofNat 256 := by
    rcases hn with rfl | rfl
    · exact Or.inl hs32
    · exact Or.inr hs32
  exact (gasSteps_common s mem hd pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
      hwidth hguard hzero).trans
    (gasSteps_setup s mem hd pa pb n pdst ret rest hcap hrun hcode hfork hnp hact
      (by rcases hn with rfl | rfl <;> omega) (by rcases hn with rfl | rfl <;> omega) hn
      hpaFit hpb hpbFit hcds hs32 hml hslot hjump)

/-- `gasSteps_commonSetup` with the staged memory written as `StagedOperand.inputMemory`
(equal to `stage` for the kernel widths), the form of WP-S1's `sqRowsCarry` start and of
`CarryResult`'s `selectedRows`. -/
opaque gasSteps_commonSetupInput (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslot : rest[2]? = some (MachineState.readWord mem 2688))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.inputMemory mem pa n) n) pb n 0 hd
        (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) := by
  have hin : StagedOperand.inputMemory mem pa n = StagedOperand.stage mem pa n := by
    unfold StagedOperand.inputMemory
    rw [if_pos (show StagedOperand.eligible mem n from ⟨hn,hguard⟩)]
  rw [hin]
  exact gasSteps_commonSetup s mem hd pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
    hpaFit hpb hpbFit hcds hs32 hml hslot hjump hguard hzero

/-- `gasSteps_setup` for the square-loop frame: the riding width slot carries the limb
count, so the row head entering the frame is the constant `3562` (the four/eight-limb
staircase is selected later, from the `tl` word at 2784). -/
opaque gasSteps_setupSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hn4 : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslotn : rest[2]? = some (UInt256.ofNat n))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true) :
    Challenge.EvmProof.GasSteps
      (CiosCached.setupState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0 hd
        (UInt256.ofNat 3562)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) :=
  setup.steps (environment (CiosCached.setupState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp)
    rfl
    (TnM128Setup.run_entry_sq s mem hd pa pb n pdst ret rest hcap hact hn hn32 hn4 hpaFit hpb hpbFit
      hcds hs32 hml hslotn (by rw [hcode]; exact hjump))

/-- `common` → `setup` with the square-loop frame's width slot (the limb count). -/
opaque gasSteps_commonSetupSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslotn : rest[2]? = some (UInt256.ofNat n))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0 hd
        (UInt256.ofNat 3562)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) := by
  have hwidth : MachineState.readWord mem 2688 = UInt256.ofNat 128 ∨
      MachineState.readWord mem 2688 = UInt256.ofNat 256 := by
    rcases hn with rfl | rfl
    · exact Or.inl hs32
    · exact Or.inr hs32
  exact (gasSteps_common s mem hd pa pb pdst ret rest (by omega) hrun hcode hfork hnp hact
      hwidth hguard hzero).trans
    (gasSteps_setupSq s mem hd pa pb n pdst ret rest hcap hrun hcode hfork hnp hact
      (by rcases hn with rfl | rfl <;> omega) (by rcases hn with rfl | rfl <;> omega) hn
      hpaFit hpb hpbFit hcds hs32 hml hslotn hjump)

/-- The square-loop entry: `gasSteps_commonSetupSq` with the staged memory written as
`StagedOperand.inputMemory` (equal to `stage` for the kernel widths). -/
opaque gasSteps_commonSetupInputSq (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslotn : rest[2]? = some (UInt256.ofNat n))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.inputMemory mem pa n) n) pb n 0 hd
        (UInt256.ofNat 3562)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) := by
  have hin : StagedOperand.inputMemory mem pa n = StagedOperand.stage mem pa n := by
    unfold StagedOperand.inputMemory
    rw [if_pos (show StagedOperand.eligible mem n from ⟨hn,hguard⟩)]
  rw [hin]
  exact gasSteps_commonSetupSq s mem hd pa pb n pdst ret rest hcap hrun hcode hfork hnp hact hn
    hpaFit hpb hpbFit hcds hs32 hml hslotn hjump hguard hzero

/-- Multiply, four or eight limbs: `mul entry` → `common` → `setup` → row-0 head at 4289
(the base's `gasSteps_dispatch4/8` followed by its `gasSteps_entry`). -/
opaque gasSteps_mulSetup (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 2816)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hslot : rest[2]? = some (MachineState.readWord mem 2688))
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0
        (UInt256.ofNat 3533) (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp).trans
    (gasSteps_commonSetup s mem (UInt256.ofNat 3533) pa pb n pdst ret rest hcap hrun hcode hfork
      hnp hact hn hpaFit hpb hpbFit hcds hs32 hml hslot jumpDestRowHead' hguard hzero)


end Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

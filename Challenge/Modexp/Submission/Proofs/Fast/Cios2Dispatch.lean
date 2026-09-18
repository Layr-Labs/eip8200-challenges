import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Kernel entry: `mul entry`, the shared `common` width guard and its fallback

The multiply is called at the `mul entry` (pc 4013) with `[pa, pb, pdst, ret] ++ rest`;
it pushes its row head `hd = 4261` and falls into `common` (pc 4104), which the square
call enters directly with `hd = 2464`.  Widths of four and eight limbs continue at the
kernel `setup` (pc 4123, `CiosCached.setupState`, `hd` on top); every other width drops
`hd` and enters the generic `MONPRO` at pc 1746 (`Monpro.mpEntryState`).

The 62-instruction `setup` (instructions 3189..3189, `StagedOperand.fullEntryProgram`,
proved piecewise in `StagedOperandEntry{Prefix,Zero}`) stages the first operand at 2368,
zeroes the scratch block and jumps (`DUP2; JUMP`) to the row head `hd` with the row-0 frame
`CiosCached.outState … 0 hd (l1Target n) …`.

Exports: `commonState` (`Exp.sqCall` is definitionally `commonState s mem 4480 512 512
(UInt256.ofNat 512) ret tail`), `gasSteps_common`, `gasSteps_commonFallback(OfWidth)`,
`gasSteps_setup`, `gasSteps_commonSetup(Input)`, and the `common`/`setup`/row-head jump
destinations.

The multiply half of this module is GONE, not renumbered: `dispatchState` (= the old
`Exp.mpCall`), `gasSteps_mulEntry`, `gasSteps_dispatch4/8` and `gasSteps_mulSetup` all began
at a `mul entry` block that this artifact does not contain -- see the note at the deletion
below.  Everything reached through `common`, which the SQUARE call enters, is unaffected.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel WindowTwentyOneBinding

-- DELETED with the 3209 multiply-entry cone.  The `mul entry` block this named --
-- `JUMPDEST; PUSH2 <mul row head>` at instruction 2386 -- is ABSENT from this artifact.
-- Its `PUSH2` was HOISTED into the fused frame program at pc 3414..3454, where the only
-- `PUSH2 3465` in the whole 5,428-byte program sits, at instruction 2766.  Measured four
-- ways: instruction 2386 is pc 2919; pc 3209 decodes to `ISZERO`; `JUMPDEST; PUSH2 3465`
-- occurs zero times; and `common` (pc 3327) is entered from exactly ONE site in the
-- artifact, `PUSH2 800; PUSH2 512; DUP1; DUP1; PUSH2 4480; PUSH2 3327; JUMP`, the SQUARE
-- call.  Absence of code, not a wrong number -- there is nothing to renumber to.
-- Deleted here: `dispatchState`, `jumpDest4012`, `run_mulEntry`, `gasSteps_mulEntry`,
-- `gasSteps_dispatch4`, `gasSteps_dispatch8`, `gasSteps_mulSetup`.  `commonState`,
-- `gasSteps_common`, `gasSteps_setup` and `gasSteps_commonSetup(Input)` all SURVIVE --
-- `common` and `setup` are real code, reached by the square call, and `SquareLoop` uses
-- them.  The cone ended at `Exp.Subroutines.monpro`, which had zero consumers tree-wide.

/-- The shared `common` block, pc 4104, with the row head `hd` above the call frame
(`hd = 4261` after the `mul entry`, `hd = 2464` for the square). -/
def commonState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3327
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }


/-- The `common` JUMPDEST (instruction 3190, pc 4104 = 0x0f54). -/
theorem jumpDestCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3327 = true := by
  exact Artifact.isValidJumpDest_index 2658 (by rfl)

/-- The kernel `setup` JUMPDEST (instruction 3190, pc 4123 = 0x0f6c). -/
theorem jumpDestSetup :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3328 = true := by
  exact Artifact.isValidJumpDest_index 2659 (by rfl)

/-- The multiply row head (instruction 1760, pc 4261 = 0x0fc5). -/
theorem jumpDestRowHead :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3465 = true := by
  exact Artifact.isValidJumpDest_index 2751 (by rfl)

/-- The square row head `sq_row` (instruction 3559, pc 2464 = 0x1266). -/
theorem jumpDestSqRow :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4179 = true := by
  exact Artifact.isValidJumpDest_index 3325 (by rfl)

/-- `jumpDestRowHead` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestRowHead' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 3465).toNat = true := by
  rw [show (UInt256.ofNat 3465).toNat = 3465 by decide]
  exact jumpDestRowHead

/-- `jumpDestSqRow` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestSqRow' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4179).toNat = true := by
  rw [show (UInt256.ofNat 4179).toNat = 4179 by decide]
  exact jumpDestSqRow

/-- The square call state (`Exp.sqCall s mem ret tail`) is definitionally `commonState`
with `hd = 2464` and `pa = pb = pdst = 2048`. -/
example (s : State) (mem : ByteArray) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3327
              stack := UInt256.ofNat 4179 :: UInt256.ofNat 512 :: UInt256.ofNat 512 ::
                UInt256.ofNat 512 :: ret :: tail
              memory := mem } : State) =
      commonState s mem 4179 512 512 (UInt256.ofNat 512) ret tail := rfl

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


/-- The kernel `setup`: instructions 3189..3189 (pc 4123 = 0x0f6c .. 4260), 62 instructions. -/
def setup : Block Artifact.submissionArtifact .Osaka 3328 StagedOperand.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2659 59 3328 StagedOperand.fullEntryProgram
    (by decide) (by decide) (by rfl) (by decide)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

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


/-- The kernel `setup` (pc 4123 → `hd`): stages `a` at 2368, zeroes `t` and builds the
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
    (StagedOperand.run_entry s mem hd pa pb n pdst ret rest hcap hact hn hn32 hn4 hpaFit hpb hpbFit
      hcds hs32 hml (by rw [hcode]; exact hjump))

/-- `common` → `setup` → row-0 head at `hd` for a four- or eight-limb width (any `hd`;
4261 for the multiply, 2464 for the square). -/
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
      hpaFit hpb hpbFit hcds hs32 hml hjump)

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
    hpaFit hpb hpbFit hcds hs32 hml hjump hguard hzero

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

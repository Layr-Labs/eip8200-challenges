import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosInverseGuard

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Kernel entry: `mul entry`, the shared `common` width guard and its fallback

The multiply is called at the `mul entry` (pc 4006) with `[pa, pb, pdst, ret] ++ rest`;
it pushes its row head `hd = 4261` and falls into `common` (pc 4097), which the square
call enters directly with `hd = 2464`.  Widths of four and eight limbs continue at the
kernel `setup` (pc 4116, `CiosCached.setupState`, `hd` on top); every other width drops
`hd` and enters the generic `MONPRO` at pc 1746 (`Monpro.mpEntryState`).

The 62-instruction `setup` (instructions 3184..3184, `StagedOperand.fullEntryProgram`,
proved piecewise in `StagedOperandEntry{Prefix,Zero}`) stages the first operand at 2368,
zeroes the scratch block and jumps (`DUP2; JUMP`) to the row head `hd` with the row-0 frame
`CiosCached.outState … 0 hd (l1Target n) …`.

Exports: `commonState` (`Exp.sqCall` is definitionally
`commonState s mem 2464 2048 2048 (UInt256.ofNat 2048) ret tail`), `dispatchState` (= `Exp.mpCall`),
`gasSteps_mulEntry`, `gasSteps_common`, `gasSteps_commonFallback(OfWidth)`, `gasSteps_setup`,
`gasSteps_commonSetup(Input)`, `gasSteps_mulSetup`, and the jump destinations 4006/4097/4116/4261/2464.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel WindowTwentyOneBinding

/-- The multiply call state: `mul entry`, pc 4006, `[pa, pb, pdst, ret] ++ rest`. -/
def dispatchState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3541
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The shared `common` block, pc 4097, with the row head `hd` above the call frame
(`hd = 4261` after the `mul entry`, `hd = 2464` for the square). -/
def commonState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3545
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- After the `common` guard's `JUMPI` falls through (pc 3897). -/
def commonFallbackState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3566
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- The `mul entry` JUMPDEST (instruction 3185, pc 4006 = 0x0f50). -/
theorem jumpDest4012 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3541 = true := by
  exact Artifact.isValidJumpDest_index 2655 (by rfl)

/-- The `common` JUMPDEST (instruction 3185, pc 4097 = 0x0f54). -/
theorem jumpDestCommon :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3545 = true := by
  exact Artifact.isValidJumpDest_index 2657 (by rfl)

/-- The kernel `setup` JUMPDEST (instruction 3185, pc 4116 = 0x0f6c). -/
theorem jumpDestSetup :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3571 = true := by
  exact Artifact.isValidJumpDest_index 2673 (by rfl)

/-- The multiply row head (instruction 1760, pc 4261 = 0x0fc5). -/
theorem jumpDestRowHead :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true := by
  exact Artifact.isValidJumpDest_index 2769 (by rfl)

/-- The square row head `sq_row` (instruction 3554, pc 2464 = 0x1266). -/
theorem jumpDestSqRow :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4471 = true := by
  exact Artifact.isValidJumpDest_index 3388 (by rfl)

/-- `jumpDestRowHead` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestRowHead' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 3711).toNat = true := by
  rw [show (UInt256.ofNat 3711).toNat = 3711 by decide]
  exact jumpDestRowHead

/-- `jumpDestSqRow` in the `hd.toNat` form taken by `gasSteps_setup`/`gasSteps_commonSetup`. -/
theorem jumpDestSqRow' :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4471).toNat = true := by
  rw [show (UInt256.ofNat 4471).toNat = 4471 by decide]
  exact jumpDestSqRow

/-- The square call state (`Exp.sqCall s mem ret tail`) is definitionally `commonState`
with `hd = 2464` and `pa = pb = pdst = 2048`. -/
example (s : State) (mem : ByteArray) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3545
              stack := UInt256.ofNat 4471 :: UInt256.ofNat 512 :: UInt256.ofNat 512 ::
                UInt256.ofNat 512 :: ret :: tail
              memory := mem } : State) =
      commonState s mem 4471 512 512 (UInt256.ofNat 512) ret tail := rfl

/-- The multiply call state (`Exp.mpCall s mem pa pb pd ret tail`) is definitionally
`dispatchState`. -/
example (s : State) (mem : ByteArray) (pa pb pd : Nat) (ret : UInt256) (tail : List UInt256) :
    ({ s with pc := UInt256.ofNat 3541
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
      some (commonState s mem (UInt256.ofNat 3711) pa pb pdst ret rest) := by
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
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 88 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat 128 ∨
      MachineState.readWord mem 2688 = UInt256.ofNat 256)
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    runInstructions commonGuardProgram (commonState s mem hd pa pb pdst ret rest) =
      some (CiosCached.setupState s mem hd pa pb pdst ret rest) := by
  have hjd : Decode.isValidJumpDest s.executionEnv.code 3571 = true := by
    rw [hcode]; exact jumpDestSetup
  simpa only [commonGuardProgram, commonState, CiosInverseGuard.stateAt,
    CiosCached.setupState] using
    CiosInverseGuard.run_guardPass s mem hd pa pb pdst ret rest hcap hact
      (CiosInverseGuard.condition_pass _ _ hs32 hzero hguard) hjd

set_option linter.unusedSimpArgs false in
/-- `common` with any other width falls through its `JUMPI` (pc 3897). -/
theorem run_commonGuardFallthrough (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : CiosInverseGuard.validWidth (MachineState.readWord mem 2688))
    (h128 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 256) :
    runInstructions commonGuardProgram (commonState s mem hd pa pb pdst ret rest) =
      some (commonFallbackState s mem hd pa pb pdst ret rest) := by
  simpa only [commonGuardProgram, commonState, commonFallbackState, CiosInverseGuard.stateAt] using
    CiosInverseGuard.run_guardFallback s mem hd pa pb pdst ret rest hcap hact
      (CiosInverseGuard.condition_width_fallback _ _ hvalid h128 h256)

theorem run_commonGuardInverseFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1008)
    (hact : 88 ≤ s.activeWords.toNat)
    (hinverse : MachineState.readWord mem 2720 = UInt256.ofNat 1) :
    runInstructions commonGuardProgram (commonState s mem hd pa pb pdst ret rest) =
      some (commonFallbackState s mem hd pa pb pdst ret rest) := by
  have hc : ¬ UInt256.isTrue (CiosInverseGuard.condition (MachineState.readWord mem 2688)
      (MachineState.readWord mem 2720)) := by
    rw [hinverse]; exact CiosInverseGuard.condition_inverse_fallback _
  simpa only [commonGuardProgram, commonState, commonFallbackState, CiosInverseGuard.stateAt] using
    CiosInverseGuard.run_guardFallback s mem hd pa pb pdst ret rest hcap hact hc

set_option linter.unusedSimpArgs false in
/-- The fallback drops `hd` and enters the generic `MONPRO` (pc 1746). -/
theorem run_commonFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions commonFallbackProgram (commonFallbackState s mem hd pa pb pdst ret rest) =
      some (mpEntryState s mem pa pb pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hjd : Decode.isValidJumpDest s.executionEnv.code 1203 = true := by
    rw [hcode]; exact jumpDest1865
  simp [commonFallbackProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    commonFallbackState, mpEntryState, hc4, hc5, hjd,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

/-- The kernel `setup`: instructions 3184..3184 (pc 4116 = 0x0f6c .. 4253), 62 instructions. -/
def setup : Block Artifact.submissionArtifact .Osaka 3571 StagedOperand.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 2673 59 3571 StagedOperand.fullEntryProgram
    (by decide) (by decide) (by rfl) (by decide)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `mul entry` → `common` with `hd = 4261`. -/
opaque gasSteps_mulEntry (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (commonState s mem (UInt256.ofNat 3711) pa pb pdst ret rest) :=
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

opaque gasSteps_commonFallback (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : CiosInverseGuard.validWidth (MachineState.readWord mem 2688))
    (h128 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 256) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest) :=
  (commonGuard.steps (environment (commonState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp) rfl
    (run_commonGuardFallthrough s mem hd pa pb pdst ret rest hcap hact hvalid h128 h256)).trans
  (commonFallback.steps (environment (commonFallbackState s mem hd pa pb pdst ret rest)
      hcode hfork hrun hnp) rfl
    (run_commonFallback s mem hd pa pb pdst ret rest hcap hcode))

/-- Multiply, four limbs: `mul entry` → `common` → `setup` with `hd = 4261`. -/
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
      (CiosCached.setupState s mem (UInt256.ofNat 3711) pa pb pdst ret rest) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest hcap hrun hcode hfork hnp).trans
    (gasSteps_common s mem (UInt256.ofNat 3711) pa pb pdst ret rest hcap hrun hcode hfork hnp
      hact (Or.inl hs32) hguard hzero)

/-- Multiply, eight limbs: `mul entry` → `common` → `setup` with `hd = 4261`. -/
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
      (CiosCached.setupState s mem (UInt256.ofNat 3711) pa pb pdst ret rest) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest hcap hrun hcode hfork hnp).trans
    (gasSteps_common s mem (UInt256.ofNat 3711) pa pb pdst ret rest hcap hrun hcode hfork hnp
      hact (Or.inr hs32) hguard hzero)

/-- Multiply, any other width: `mul entry` → `common` → generic `MONPRO`. -/
opaque gasSteps_dispatchFallback (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat)
    (hvalid : CiosInverseGuard.validWidth (MachineState.readWord mem 2688))
    (h128 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 256) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest hcap hrun hcode hfork hnp).trans
    (gasSteps_commonFallback s mem (UInt256.ofNat 3711) pa pb pdst ret rest hcap hrun hcode
      hfork hnp hact hvalid h128 h256)

/-- `common` → generic `MONPRO` stated with the width word: `S32 = 32 * n` with `n ∉ {4, 8}`. -/
opaque gasSteps_commonFallbackOfWidth (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (hn4 : n ≠ 4) (hn8 : n ≠ 8) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest) := by
  have hvalid : CiosInverseGuard.validWidth (MachineState.readWord mem 2688) :=
    ⟨n, hn, hn32, hs32⟩
  have h32n : 32 * n < 2 ^ 256 := by omega
  have h128 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 128 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 128 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn4 (by omega)
  have h256 : MachineState.readWord mem 2688 ≠ UInt256.ofNat 256 := by
    intro heq
    have hword : UInt256.ofNat (32 * n) = UInt256.ofNat 256 := hs32.symm.trans heq
    have hnat := congrArg UInt256.toNat hword
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt h32n,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hn8 (by omega)
  exact gasSteps_commonFallback s mem hd pa pb pdst ret rest hcap hrun hcode hfork hnp hact hvalid h128 h256

/-- The kernel `setup` (pc 4116 → `hd`): stages `a` at 2368, zeroes `t` and builds the
row-0 frame `[pbi, hd, pb-32, l1Target n, …, inv, m0, tl, m96, m64, m32, aEnd, pdst, ret]`. -/
opaque gasSteps_setup (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
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
    (StagedOperand.run_entry s mem hd pa pb n pdst ret rest hcap hact hn hn32 hpaFit hpb hpbFit
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
      (by omega) (by omega) hpaFit hpb hpbFit hcds hs32 hml hjump)

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

/-- Multiply, four or eight limbs: `mul entry` → `common` → `setup` → row-0 head at 4261
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
    (hguard : MachineState.readWord mem 2720 ≠ UInt256.ofNat 1)
    (hzero : MachineState.readWord mem 2720 ≠ UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (CiosCached.outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0
        (UInt256.ofNat 3711) (CiosCached.l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32 * n - 32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa + 32 * n - 32) :: pdst :: ret :: rest)) :=
  (gasSteps_mulEntry s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp).trans
    (gasSteps_commonSetup s mem (UInt256.ofNat 3711) pa pb n pdst ret rest hcap hrun hcode hfork
      hnp hact hn hpaFit hpb hpbFit hcds hs32 hml jumpDestRowHead' hguard hzero)

/-- A rejected inverse uses the same generic ABI as a rejected width. -/
opaque gasSteps_commonFallbackEligible (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hslow : ¬ StagedOperand.eligible mem n) :
    Challenge.EvmProof.GasSteps
      (commonState s mem hd pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest) := by
  by_cases hw : n = 4 ∨ n = 8
  · have hi : MachineState.readWord mem 2720 = UInt256.ofNat 1 := by
      by_contra hi
      exact hslow ⟨hw,hi⟩
    exact (commonGuard.steps (environment (commonState s mem hd pa pb pdst ret rest) hcode hfork hrun hnp) rfl
      (run_commonGuardInverseFallback s mem hd pa pb pdst ret rest hcap hact hi)).trans
      (commonFallback.steps (environment (commonFallbackState s mem hd pa pb pdst ret rest)
        hcode hfork hrun hnp) rfl
        (run_commonFallback s mem hd pa pb pdst ret rest hcap hcode))
  · exact gasSteps_commonFallbackOfWidth s mem hd pa pb n pdst ret rest hcap hrun hcode
      hfork hnp hact hn hn32 hs32 (fun h => hw (Or.inl h)) (fun h => hw (Or.inr h))

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

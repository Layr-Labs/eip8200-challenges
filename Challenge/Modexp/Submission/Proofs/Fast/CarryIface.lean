import Challenge.Modexp.Submission.Proofs.Fast.CarryResult
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandCarrySnapshot
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Interface of the multiply composition (WP-K3)

`CarryRows` / `CarryFull*` compose the sqCP1m multiply kernel out of the block traces of
WP-K (one kernel row, `CarryRowGas`) and WP-K2 (the kernel entry: `mul entry`, `common`,
`setup`, fallback; `Cios2Dispatch`).  The composition is written generically over the two
bundles below, whose fields are exactly the statements of those lemmas (explicit
hypotheses — no axiom, no `sorry`).  They are instantiated with the real lemmas by
`CarryIface.rowLemmas` (`CarryRowLemmas`) and `CarryIface.entryLemmas` (`CarryEntryLemmas`),
and `CarryFull.gasSteps_monproFull` (`CarryFullMonproFinal`) applies the generic composition
`CarryFull.gasSteps_monproFullOf` to them.

* `RowLemmas`   : WP-K `CarryRowGas.*` (stage 2, frames with row head `hd` and entry `ent`).
* `EntryLemmas` : WP-K2 `Cios2Dispatch.*`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryIface

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CarryRowModel CiosCachedMidMemory

set_option linter.unusedVariables false in
/-- The block traces of one multiply row (WP-K stage 2, `CarryRowGas`).  (The binder names
of the fields only document the hypotheses; the unused-variable linter is off for them.)
Instantiated by `rowLemmas` (`CarryRowLemmas`). -/
structure RowLemmas : Type where
  /-- Statement of WP-K `CarryRowGas.gasSteps_out`. -/
  gasSteps_out : ∀ (s : State) (mem : ByteArray) (pb n i : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376),
    Challenge.EvmProof.GasSteps
      (outState s mem pb n i (UInt256.ofNat 4029) ent pdst ret rest)
      (firstAt 4032 s mem (rowBi mem pb n i) pb n i (UInt256.ofNat 4029) ent pdst ret rest)
  /-- Statement of WP-K `CarryRowGas.gasSteps_commonFirst`. -/
  gasSteps_commonFirst : ∀ (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 5376)
    (htl : tl = UInt256.ofNat (4128+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)),
    Challenge.EvmProof.GasSteps
      (firstAt 4032 s mem bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l1At 4058 s mem bi pa pb n i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
  /-- Statement of WP-K `CarryRowGas.gasSteps_l1MulFour`. -/
  gasSteps_l1MulFour : ∀ (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 4096) (hsnapshot : StagedOperand.Snapshot mem pa 4),
    Challenge.EvmProof.GasSteps
      (l1At 4058 s mem bi pa pb 4 i 1 hd (l1Target 4) pdst ret rest)
      (midState s (l1Step mem bi pa 4 4).memory (l1Step mem bi pa 4 4).carry bi
        pb 4 i hd (l1Target 4) pdst ret rest)
  /-- Statement of WP-K `CarryRowGas.gasSteps_l1MulEight`. -/
  gasSteps_l1MulEight : ∀ (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 4096) (hsnapshot : StagedOperand.Snapshot mem pa 8),
    Challenge.EvmProof.GasSteps
      (l1At 4058 s mem bi pa pb 8 i 1 hd (l1Target 8) pdst ret rest)
      (midState s (l1Step mem bi pa 8 8).memory (l1Step mem bi pa 8 8).carry bi
        pb 8 i hd (l1Target 8) pdst ret rest)
  /-- Statement of WP-K `CarryRowGas.gasSteps_mid`. -/
  gasSteps_mid : ∀ (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0),
    Challenge.EvmProof.GasSteps
      (midState s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 4357 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
  /-- Statement of WP-K `CarryRowGas.gasSteps_l2Four`. -/
  gasSteps_l2Four : ∀ (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32),
    Challenge.EvmProof.GasSteps
      (l2At 4357 s mid bi mu c0 pb 4 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 4 3).memory
        (l2Step mid mu c0 4 3).carry mu bi pb 4 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
  /-- Statement of WP-K `CarryRowGas.gasSteps_l2Eight`. -/
  gasSteps_l2Eight : ∀ (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32),
    Challenge.EvmProof.GasSteps
      (l2At 4357 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 8 7).memory
        (l2Step mid mu c0 8 7).carry mu bi pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
  /-- Statement of WP-K `CarryRowGas.gasSteps_tailNext`. -/
  gasSteps_tailNext : ∀ (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true),
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pb n i hd ent pdst ret rest)
      (outState s (tailCarry mem c bi) pb n (i + 1) hd ent pdst ret rest)
  /-- Statement of WP-K `CarryRowGas.gasSteps_tailLast`. -/
  gasSteps_tailLast : ∀ (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hne : hd ≠ UInt256.ofNat 4788),
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (tailCarry mem c bi) pdst ret rest)

set_option linter.unusedVariables false in
/-- The kernel entry (WP-K2, `Cios2Dispatch`).  Instantiated by `entryLemmas` (`CarryEntryLemmas`). -/
structure EntryLemmas : Type where
  /-- Statement of WP-K2 `Cios2Dispatch.gasSteps_mulEntry`: `mul entry` (pc 3920) →
  `common` (pc 3924) with the multiply row head `hd = 4037`. -/
  gasSteps_mulEntry : ∀ (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false),
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.dispatchState s mem pa pb pdst ret rest)
      (Cios2Dispatch.commonState s mem (UInt256.ofNat 4029) pa pb pdst ret rest)
  /-- Statement of WP-K2 `Cios2Dispatch.gasSteps_commonSetup`: `common` → `setup` →
  row 0 at `hd` (widths four and eight limbs). -/
  gasSteps_commonSetup : ∀ (s : State) (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat) (hn : n = 4 ∨ n = 8)
    (hpaFit : pa + 32 * n ≤ 5376)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 5376)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 5248 = UInt256.ofNat (32 * n))
    (hml : MachineState.readWord mem 5312 = UInt256.ofNat (32 * n - 32))
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true),
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.commonState s mem hd pa pb pdst ret rest)
      (outState s (mpZeroed s (StagedOperand.stage mem pa n) n) pb n 0 hd (l1Target n)
        (MachineState.readWord mem 5280) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 5344 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: pdst :: ret :: rest))
  /-- Statement of WP-K2 `Cios2Dispatch.gasSteps_commonFallback`: every other width
  drops `hd` and enters the generic `MONPRO` (pc 1667). -/
  gasSteps_commonFallback : ∀ (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 168 ≤ s.activeWords.toNat)
    (h128 : MachineState.readWord mem 5248 ≠ UInt256.ofNat 128)
    (h256 : MachineState.readWord mem 5248 ≠ UInt256.ofNat 256),
    Challenge.EvmProof.GasSteps
      (Cios2Dispatch.commonState s mem hd pa pb pdst ret rest)
      (mpEntryState s mem pa pb pdst ret rest)

/-- The multiply row head `hd = 4037` (instruction 3040, pc 0x0fc5) is a jump destination. -/
theorem jumpDest_rowHead :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode (UInt256.ofNat 4029).toNat = true := by
  rw [show (UInt256.ofNat 4029).toNat = 4029 from by decide]
  exact Artifact.isValidJumpDest_index 3032 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CarryIface

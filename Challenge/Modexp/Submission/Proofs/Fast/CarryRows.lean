import Challenge.Modexp.Submission.Proofs.Fast.CarryIface

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Fixed-width CIOS row schedules of the sqCP1m multiply kernel

The kernel admits only four- and eight-limb inputs.  A multiply row starts at the row
head `hd = 3481` with the first-loop entry `ent = l1Base n` and the carry cell `cy` in its frame: the row head
and first product (`out`, `commonFirst`), the `DUP6 JUMP` into the uniform first-loop
chain (block `k = 5` for four limbs, `k = 1` for eight), the middle block, the second
loop, and the row end `DUP3 JUMPI` back to `hd` (or the exit to the final subtraction).
The block traces come from `CarryIface.RowLemmas`; the arithmetic state stays in the
existing `Monpro` model.  There is no new arithmetic identity here.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

open CiosCached CarryIface
open CiosCachedMidMemory CarryRowModel

/-- One complete four-limb row, stopping at the common tail block. -/
opaque gasSteps_rowFourToTail (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 4 i (UInt256.ofNat 3481) (l1Base 4) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (fromL2S (rowL1 mem pa pb 4 i) 4).memory
        (fromL2S (rowL1 mem pa pb 4 i) 4).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4)
        (slotOverflow cy (rowL1 mem pa pb 4 i).carry) pb 4 i (UInt256.ofNat 3481) (l1Base 4)
        (cy + (rowL1 mem pa pb 4 i).carry) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hminvN := inverse_l1Step mem (rowBi mem pb 4 i) pa 4 4 (by decide) hminv
  refine (L.gasSteps_out s mem pb 4 i (l1Base 4) cy inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpb hpbFit).trans ?_
  refine (L.gasSteps_commonFirst s mem (rowBi mem pb 4 i) pa pb 4 i
    (UInt256.ofNat 3481) (l1Base 4) cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode
    hfork hnp hact (by decide) (by decide) (by omega) hc.lowAddress hAend).trans ?_
  refine (L.gasSteps_l1MulFour s mem (rowBi mem pb 4 i) pa pb i (UInt256.ofNat 3481) cy inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact
    hpaFit hsnapshot).trans ?_
  refine (L.gasSteps_midCopy s (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry (rowBi mem pb 4 i)
    pb 4 i (UInt256.ofNat 3481) (l1Base 4) cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
    hrun hcode hfork hnp hact (by decide) (by decide) hminvN
    (hc.l1 (by decide) (rowBi mem pb 4 i) pa 4)).trans ?_
  simpa only [rowL1, fromL2S] using
    L.gasSteps_l2Four s (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
      (slotOverflow cy (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry)
      (rowMu (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      (rowC0 (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      pb i (UInt256.ofNat 3481) (l1Base 4) (cy + (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry)
      tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (he.l1 (rowBi mem pb 4 i) pa 4 4 (by decide))

/-- One complete eight-limb row, stopping at the common tail block. -/
opaque gasSteps_rowEightToTail (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 8 i (UInt256.ofNat 3481) (l1Base 8) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (fromL2S (rowL1 mem pa pb 8 i) 8).memory
        (fromL2S (rowL1 mem pa pb 8 i) 8).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8)
        (slotOverflow cy (rowL1 mem pa pb 8 i).carry) pb 8 i (UInt256.ofNat 3481) (l1Base 8)
        (cy + (rowL1 mem pa pb 8 i).carry) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  have hminvN := inverse_l1Step mem (rowBi mem pb 8 i) pa 8 8 (by decide) hminv
  refine (L.gasSteps_out s mem pb 8 i (l1Base 8) cy inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpb hpbFit).trans ?_
  refine (L.gasSteps_commonFirst s mem (rowBi mem pb 8 i) pa pb 8 i
    (UInt256.ofNat 3481) (l1Base 8) cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode
    hfork hnp hact (by decide) (by decide) (by omega) hc.lowAddress hAend).trans ?_
  refine (L.gasSteps_l1MulEight s mem (rowBi mem pb 8 i) pa pb i (UInt256.ofNat 3481) cy inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact
    hpaFit hsnapshot).trans ?_
  refine (L.gasSteps_mid s (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry (rowBi mem pb 8 i)
    pb 8 i (UInt256.ofNat 3481) (l1Base 8) cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
    hrun hcode hfork hnp hact (by decide) (by decide) hminvN
    (hc.l1 (by decide) (rowBi mem pb 8 i) pa 8)).trans ?_
  simpa only [rowL1, fromL2S] using
    L.gasSteps_l2Eight s (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
      (slotOverflow cy (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry)
      (rowMu (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      (rowC0 (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      pb i (UInt256.ofNat 3481) (l1Base 8) (cy + (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry)
      tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (he.l1 (rowBi mem pb 8 i) pa 8 8 (by decide))

/-- A four-limb row that is not the last: back to the row head `hd = 3481` with the
row's carry out in the cell. -/
opaque gasSteps_rowFourNext (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i + 1 < 4)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 4 i (UInt256.ofNat 3481) (l1Base 4) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (outState s (rowMemS mem cy pa pb 4 i) pb 4 (i + 1) (UInt256.ofNat 3481) (l1Base 4)
        (rowSlot mem cy pa pb 4 i) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (gasSteps_rowFourToTail L s mem pa pb i cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun
      hcode hfork hnp hact (by omega) hpaFit hpb hpbFit hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowMemS, rowSlot, fromMemS, fromSlot] using
      L.gasSteps_tailNext s (fromL2S (rowL1 mem pa pb 4 i) 4).memory
        (fromL2S (rowL1 mem pa pb 4 i) 4).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (slotOverflow cy (rowL1 mem pa pb 4 i).carry)
        pb 4 i (UInt256.ofNat 3481) (l1Base 4) (cy + (rowL1 mem pa pb 4 i).carry) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
        (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi hpb hpbFit
        jumpDest_rowHead

/-- The last four-limb row: through the exit (the cell flushed to `mem[2080]`) to
the final subtraction (pc 4086). -/
opaque gasSteps_rowFourLast (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i + 1 = 4)
    (hpaFit : pa + 32 * 4 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 2816)
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 4 i (UInt256.ofNat 3481) (l1Base 4) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (flushS (rowMemS mem cy pa pb 4 i) (rowSlot mem cy pa pb 4 i)) pdst ret rest) :=
  (gasSteps_rowFourToTail L s mem pa pb i cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun
      hcode hfork hnp hact (by omega) hpaFit hpb hpbFit hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowMemS, rowSlot, fromMemS, fromSlot] using
      L.gasSteps_tailLast s (fromL2S (rowL1 mem pa pb 4 i) 4).memory
        (fromL2S (rowL1 mem pa pb 4 i) 4).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (slotOverflow cy (rowL1 mem pa pb 4 i).carry)
        pb 4 i (UInt256.ofNat 3481) (l1Base 4) (cy + (rowL1 mem pa pb 4 i).carry)
        tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
        hrun hcode hfork hnp hact hi hpb hpbFit jumpDest_rowHead (by decide)

/-- An eight-limb row that is not the last: back to the row head `hd = 3481` with the
row's carry out in the cell. -/
opaque gasSteps_rowEightNext (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i + 1 < 8)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 8 i (UInt256.ofNat 3481) (l1Base 8) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (outState s (rowMemS mem cy pa pb 8 i) pb 8 (i + 1) (UInt256.ofNat 3481) (l1Base 8)
        (rowSlot mem cy pa pb 8 i) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (gasSteps_rowEightToTail L s mem pa pb i cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun
      hcode hfork hnp hact (by omega) hpaFit hpb hpbFit hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowMemS, rowSlot, fromMemS, fromSlot] using
      L.gasSteps_tailNext s (fromL2S (rowL1 mem pa pb 8 i) 8).memory
        (fromL2S (rowL1 mem pa pb 8 i) 8).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (slotOverflow cy (rowL1 mem pa pb 8 i).carry)
        pb 8 i (UInt256.ofNat 3481) (l1Base 8) (cy + (rowL1 mem pa pb 8 i).carry) inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
        (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact hi hpb hpbFit
        jumpDest_rowHead

/-- The last eight-limb row: through the exit (the cell flushed to `mem[2080]`) to
the final subtraction (pc 4086). -/
opaque gasSteps_rowEightLast (L : RowLemmas) (s : State) (mem : ByteArray) (pa pb i : Nat)
    (cy tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hi : i + 1 = 8)
    (hpaFit : pa + 32 * 8 ≤ 2048 ∨ pa = 2368)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 2816)
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb 8 i (UInt256.ofNat 3481) (l1Base 8) cy inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (flushS (rowMemS mem cy pa pb 8 i) (rowSlot mem cy pa pb 8 i)) pdst ret rest) :=
  (gasSteps_rowEightToTail L s mem pa pb i cy tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun
      hcode hfork hnp hact (by omega) hpaFit hpb hpbFit hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowMemS, rowSlot, fromMemS, fromSlot] using
      L.gasSteps_tailLast s (fromL2S (rowL1 mem pa pb 8 i) 8).memory
        (fromL2S (rowL1 mem pa pb 8 i) 8).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (slotOverflow cy (rowL1 mem pa pb 8 i).carry)
        pb 8 i (UInt256.ofNat 3481) (l1Base 8) (cy + (rowL1 mem pa pb 8 i).carry)
        tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
        hrun hcode hfork hnp hact hi hpb hpbFit jumpDest_rowHead (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.CarryRows

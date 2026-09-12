import Challenge.Modexp.Submission.Proofs.Fast.KernelChain
import Challenge.Modexp.Submission.Proofs.Fast.CarryReadonlyRun
import Challenge.Modexp.Submission.Proofs.Fast.CiosCommonFirst
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedOut
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyTraces
import Challenge.Modexp.Submission.Proofs.Fast.CarryTailRows
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMac
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedControl

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# Gas-parametric block traces of one kernel row (stage 2)

Every lemma is stated on the row frames of `CiosCachedFrames` / `CiosCachedRowFrames`,
generic in the row head `hd` and the first-loop entry `ent` (the multiply instantiates
`hd = 4037`, `ent = l1Target n`; the square rows `hd = 4710` and their own `ent`), and in
the memory/carry.  Multiply-only pieces: the row head `out` (pc 4037), `commonFirst`,
and `gasSteps_l1MulFour/Eight` (the `DUP6 JUMP` dispatch + the uniform chain).
Shared: `gasSteps_mid` (4334 → 4365), `gasSteps_l2Four/Eight` (4365 → 4623),
`gasSteps_tailNext` (4623 → next row head `hd`), `gasSteps_tailLast` (4623 → CSUB 4667).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open CiosCached CarryRowBlocks CarryRowModel
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

/-! ## Multiply row head and first product -/

/-- Multiply row head (`hd = 4037`): `JUMPDEST; DUP1; MLOAD` loads `b_i`. -/
opaque gasSteps_out (s : State) (mem : ByteArray) (pb n i : Nat)
    (ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hi : i < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (outState s mem pb n i (UInt256.ofNat 4018) ent pdst ret rest)
      (firstAt 4021 s mem (rowBi mem pb n i) pb n i (UInt256.ofNat 4018) ent pdst ret rest) :=
  CarryRowBlocks.out.steps
    (environment (outState s mem pb n i (UInt256.ofNat 4018) ent pdst ret rest) hcode hfork hrun hnp)
    rfl
    (run_out s mem pb n i ent pdst ret rest hcap hrun hact hn hn32 hi hpb hpbFit)

/-- The first product of a multiply row (carry zero), pc 4040 → 4066. -/
opaque gasSteps_commonFirst (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hpos : 0 < n)
    (hpaFit : pa+32*n ≤ 9472)
    (htl : tl = UInt256.ofNat (8224+32*n))
    (hAend : aEnd = UInt256.ofNat (pa+32*n-32)) :
    Challenge.EvmProof.GasSteps
      (firstAt 4021 s mem bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l1At 4047 s mem bi pa pb n i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  l1Mac0.steps (environment _ hcode hfork hrun hnp) rfl
    (CiosCommonFirst.run_commonFirst s mem bi pa pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest
      hcap hact hn hpos hpaFit htl hAend)

/-! ## Multiply first loop: `DUP6 JUMP` to `ent = l1Target n`, then the uniform chain -/

opaque gasSteps_l1Dispatch4 (s : State) (q : MacState) (bi : UInt256)
    (pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1Q 4047 s q bi pb 4 i hd (l1Target 4) pdst ret rest)
      (l1Q 4201 s q bi pb 4 i hd (l1Target 4) pdst ret rest) :=
  l1Dispatch.steps (environment (l1Q 4047 s q bi pb 4 i hd (l1Target 4) pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch4 s q bi pb i hd pdst ret rest hcap
      (by rw [hcode]; exact KernelChain.jumpDest4220))

opaque gasSteps_l1Dispatch8 (s : State) (q : MacState) (bi : UInt256)
    (pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l1Q 4047 s q bi pb 8 i hd (l1Target 8) pdst ret rest)
      (l1Q 4049 s q bi pb 8 i hd (l1Target 8) pdst ret rest) :=
  l1Dispatch.steps (environment (l1Q 4047 s q bi pb 8 i hd (l1Target 8) pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l1Dispatch8 s q bi pb i hd pdst ret rest hcap
      (by rw [hcode]; exact KernelChain.jumpDest4068))

/-- Four-limb multiply row: dispatch to block `k = 5` (pc 4220) and run steps `1..3`. -/
opaque gasSteps_l1MulFour (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 4 ≤ 8192) (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (l1At 4047 s mem bi pa pb 4 i 1 hd (l1Target 4) pdst ret rest)
      (midState s (l1Step mem bi pa 4 4).memory (l1Step mem bi pa 4 4).carry bi
        pb 4 i hd (l1Target 4) pdst ret rest) :=
  (gasSteps_l1Dispatch4 s (l1Step mem bi pa 4 1) bi pb i hd pdst ret rest hcap hrun hcode hfork hnp).trans
    (KernelChain.gasSteps_l1SuffixMul 5 (by decide) (by decide) s mem bi pa pb 4 i 1 hd (l1Target 4)
      pdst ret rest hcap hrun hcode hfork hnp hact (by decide) hpaFit (by decide) hsnapshot)

/-- Eight-limb multiply row: dispatch to block `k = 1` (pc 4068) and run steps `1..7`. -/
opaque gasSteps_l1MulEight (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (hd pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpaFit : pa + 32 * 8 ≤ 8192) (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (l1At 4047 s mem bi pa pb 8 i 1 hd (l1Target 8) pdst ret rest)
      (midState s (l1Step mem bi pa 8 8).memory (l1Step mem bi pa 8 8).carry bi
        pb 8 i hd (l1Target 8) pdst ret rest) :=
  (gasSteps_l1Dispatch8 s (l1Step mem bi pa 8 1) bi pb i hd pdst ret rest hcap hrun hcode hfork hnp).trans
    (KernelChain.gasSteps_l1SuffixMul 1 (by decide) (by decide) s mem bi pa pb 8 i 1 hd (l1Target 8)
      pdst ret rest hcap hrun hcode hfork hnp hact (by decide) hpaFit (by decide) hsnapshot)

/-! ## The middle block (pc 4334 → 4365), shared -/

opaque gasSteps_mid (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hminv : inverseInvariant mem n)
    (hc : CiosReadonly.ReadonlyCache mem n tl inv m0) :
    Challenge.EvmProof.GasSteps
      (midState s mem c bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At 4346 s (midMem1 mem c) (overflow mem c) (rowMu mem n)
        (rowC0 mem n) pb n i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  CarryRowBlocks.mid.steps (environment _ hcode hfork hrun hnp) rfl
    (CarryReadonlyRun.run_middle s mem c bi pb n i hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact
      hn hn32 hc hminv)

/-! ## Second loop (pc 4365 → 4623), shared -/

opaque gasSteps_l2Mac (pc : Nat) (w : Fin 33) (x tl ts : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc (l2Program w x tl ts))
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32 * (n - 2 - k)) (htl : tl.toNat = 8256 + 32 * (n - 2 - k))
    (hts : ts.toNat = 8256 + 32 * (n - 1 - k))
    (hpush : w.val = 0 → x = UInt256.ofNat 0) :
    Challenge.EvmProof.GasSteps
      (l2At pc s mem bi mu c0 pb n i k hd ent pdst ret rest)
      (l2At (pc+(w.val+35)) s mem bi mu c0 pb n i (k+1) hd ent pdst ret rest) :=
  block.steps (environment (l2At pc s mem bi mu c0 pb n i k hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Mac pc w x tl ts s mem bi mu c0 pb n i k hd ent pdst ret rest hcap hact hn32 hk hx htl hts hpush)

opaque gasSteps_extraL2 (slot : Fin 3) (pc : Nat) (x loadAddr storeAddr : UInt256)
    (block : Block Artifact.submissionArtifact .Osaka pc
      (CiosReadonlyExtra.extraProgram slot loadAddr storeAddr))
    (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32) (hk : k+1 < n)
    (hx : x.toNat = 32*(n-2-k)) (hselect : x.toNat = CiosReadonlyExtra.cacheAddress slot)
    (hload : loadAddr.toNat = 8256+32*(n-2-k))
    (hstore : storeAddr.toNat = 8256+32*(n-1-k))
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At pc s mem bi mu c0 pb n i k hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (l2At (pc+34) s mem bi mu c0 pb n i (k+1) hd ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have h := CiosReadonlyExtra.run_extraStep slot s (UInt256.ofNat pc) mem
    bi mu c0 n k x loadAddr storeAddr hx hselect hload hstore
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) hd
    (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hact hn hk hc
  exact block.steps (environment _ hcode hfork hrun hnp) rfl
    (by simpa only [CiosCachedL2.state,l2At,Challenge.EvmProof.Word.ofNat_add_mod,
      List.cons_append,List.nil_append] using h)

opaque gasSteps_l2Dispatch4 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4346 s mem bi mu c0 pb 4 i k hd ent pdst ret rest)
      (l2At 4500 s mem bi mu c0 pb 4 i k hd ent pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4346 s mem bi mu c0 pb 4 i k hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch4 s mem bi mu c0 pb i k hd ent pdst ret rest hcap
      (by rw [hcode]; exact jumpDest5112))

opaque gasSteps_l2Dispatch8 (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4346 s mem bi mu c0 pb 8 i k hd ent pdst ret rest)
      (l2At 4349 s mem bi mu c0 pb 8 i k hd ent pdst ret rest) :=
  l2Dispatch.steps (environment (l2At 4346 s mem bi mu c0 pb 8 i k hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Dispatch8 s mem bi mu c0 pb i k hd ent pdst ret rest hcap
      (by rw [hcode]; exact jumpDestL2Eight)) |>.trans
  (l2Join8.steps (environment (l2At 4348 s mem bi mu c0 pb 8 i k hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join8 s mem bi mu c0 pb 8 i k hd ent pdst ret rest hcap))

opaque gasSteps_l2Join (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i k : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (l2At 4500 s mem bi mu c0 pb n i k hd ent pdst ret rest)
      (l2At 4501 s mem bi mu c0 pb n i k hd ent pdst ret rest) :=
  l2Join.steps (environment (l2At 4500 s mem bi mu c0 pb n i k hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (run_l2Join s mem bi mu c0 pb n i k hd ent pdst ret rest hcap)

/-- The final second-loop copy lands exactly on the row tail frame. -/
opaque gasSteps_l2Final (s : State) (mem : ByteArray) (bi mu c0 : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hn : 2 ≤ n) :
    Challenge.EvmProof.GasSteps
      (l2At 4569 s mem bi mu c0 pb n i (n-2) hd ent pdst ret rest)
      (tailState s (l2Step mem mu c0 n (n-1)).memory
        (l2Step mem mu c0 n (n-1)).carry mu bi pb n i hd ent pdst ret rest) := by
  have h := gasSteps_l2Mac 4569 0 0 8256 8288 l2Mac6 s mem bi mu c0 pb n i (n-2) hd ent pdst ret rest
    hcap hrun hcode hfork hnp hact hn32 (by omega)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 2 - (n - 2) = 0 by omega]; decide)
    (by rw [show n - 1 - (n - 2) = 1 by omega]; decide) (by decide)
  have hnn : n - 2 + 1 = n - 1 := by omega
  rw [hnn] at h
  exact h

/-- The whole four-limb second loop (dispatch to 4519, three cells). -/
opaque gasSteps_l2Four (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 4346 s mid bi mu c0 pb 4 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 4 3).memory
        (l2Step mid mu c0 4 3).carry mu bi pb 4 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch4 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_l2Join s mid bi mu c0 pb 4 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_extraL2 1 4501 64 8320 8352 l2Mac4 s mid bi mu c0 pb 4 i 0 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_extraL2 2 4535 32 8288 8320 l2Mac5 s mid bi mu c0 pb 4 i 1 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2Final s mid bi mu c0 pb 4 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

/-- The whole eight-limb second loop (dispatch to 4367, seven cells). -/
opaque gasSteps_l2Eight (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pb i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 4346 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 8 7).memory
        (l2Step mid mu c0 8 7).carry mu bi pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8 s mid bi mu c0 pb i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_l2Mac 4349 10 192 8448 8480 l2Mac0 s mid bi mu c0 pb 8 i 0 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 4394 1 160 8416 8448 l2Mac1 s mid bi mu c0 pb 8 i 1 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 4430 1 128 8384 8416 l2Mac2 s mid bi mu c0 pb 8 i 2 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_extraL2 0 4466 96 8352 8384 l2Mac3 s mid bi mu c0 pb 8 i 3 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2Join s mid bi mu c0 pb 8 i 4 hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_extraL2 1 4501 64 8320 8352 l2Mac4 s mid bi mu c0 pb 8 i 4 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_extraL2 2 4535 32 8288 8320 l2Mac5 s mid bi mu c0 pb 8 i 5 hd ent tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2Final s mid bi mu c0 pb 8 i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

/-! ## Row end (pc 4623): `DUP3 JUMPI` back to the row head `hd`, or the exit to CSUB -/

/-- Not the last row: store the top words and jump back to the frame's row head `hd`. -/
opaque gasSteps_tailNext (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 < n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true) :
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pb n i hd ent pdst ret rest)
      (outState s (tailCarry mem c bi) pb n (i + 1) hd ent pdst ret rest) :=
  tailLoop.steps (environment (tailState s mem c mu bi pb n i hd ent pdst ret rest) hcode hfork hrun hnp) rfl
    (CarryTailRows.run_next s mem c mu bi pb n i hd ent pdst ret rest
      hcap hact hpb hpbFit hi (by rw [hcode]; exact hhd))

/-! ## R0: the kernel-exit dispatch (pc 4630)

The row loop's `DUP3 JUMPI` now falls through into `DUP2 PUSH2 sq_row EQ PUSH2 sq_exit
JUMPI`.  A square (`hd = sq_row = 4777`) leaves through `sq_exit` with its frame intact
(`SquareLoop`); every multiply — and every square row that is not the last — is unaffected
because the dispatch only reads the frame's row head. -/

private theorem toNat_ne_of_ne {a b : UInt256} (h : a ≠ b) : a.toNat ≠ b.toNat := by
  intro hab
  apply h
  cases a with
  | mk av =>
    cases b with
    | mk bv =>
      simp only [UInt256.toNat] at hab
      congr
      exact Fin.ext hab

theorem jumpDest4726 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4701 = true :=
  Artifact.isValidJumpDest_index 3583 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4639 = true :=
  Artifact.isValidJumpDest_index 3538 (by rfl)

/-! ## R0: the kernel-exit dispatch (pc 4630)

`DUP2 PUSH2 sq_row EQ PUSH2 sq_exit JUMPI`: the frame's row head decides.  A square
(`hd = sq_row = 4777`) jumps to `sq_exit` (4701) with the frame retained; every multiply
falls through the `JUMPI` into the `nx` `JUMPDEST` (4639) and on to the 14 `POP`s. -/

def dispatchProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 2 4777, .op .EQ, .push 2 4701, .op .JUMPI]

/-- The dispatch block: the `JUMPI` ends it, taken for a square and not taken for a
multiply (which then continues at the `nx` `JUMPDEST` 4639). -/
def dispatchBlock : Block Artifact.submissionArtifact .Osaka 4630 dispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3533 5 4630 dispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The `nx` `JUMPDEST` (reached by the dispatch's fall-through and by `sq_exit`'s last
square). -/
def nxJd : Block Artifact.submissionArtifact .Osaka 4639 [.op .JUMPDEST] :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3538 1 4639 [.op .JUMPDEST]
    (by decide) (by rfl) (by rfl) (by decide)

set_option linter.unusedSimpArgs false in
/-- A multiply falls through the dispatch into the `nx` `JUMPDEST` (4639 → 4640). -/
theorem run_dispatchMul (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (hd ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hne : hd ≠ UInt256.ofNat 4777) :
    runInstructions dispatchProgram
      (CiosCachedTailDefs.exitState s mem pbi pb n hd ent dst ret rest) =
    some (CiosCachedTailDefs.nxJdState s mem pbi pb n hd ent dst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hcond : ¬ UInt256.isTrue ((UInt256.ofNat 4777).eq hd) := by
    rw [UInt256.eq]
    simp only [if_neg (toNat_ne_of_ne (Ne.symm hne))]
    decide
  simp [dispatchProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, CiosCachedTailDefs.exitState,
    CiosCachedTailDefs.nxJdState, CiosCachedMacCore.framed, hc9, hc10, hc11, hcond,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
/-- A square takes the dispatch's `JUMPI` to `sq_exit` (4701) with the frame retained. -/
theorem run_dispatchSq (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode) :
    runInstructions dispatchProgram
      (CiosCachedTailDefs.exitState s mem pbi pb n (UInt256.ofNat 4777) ent dst ret rest) =
    some (CiosCachedTailDefs.sqExitState s mem pbi pb n (UInt256.ofNat 4777) ent dst ret rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hcond : UInt256.isTrue ((UInt256.ofNat 4777).eq (UInt256.ofNat 4777)) := by decide
  have hjd : Decode.isValidJumpDest s.executionEnv.code 4701 = true := by
    rw [hcode]; exact jumpDest4726
  simp [dispatchProgram, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, CiosCachedTailDefs.exitState,
    CiosCachedTailDefs.sqExitState, CiosCachedMacCore.framed, hc9, hc10, hc11, hcond, hjd,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
/-- The `nx` `JUMPDEST` alone (4639 → 4640), used by the last square's exit. -/
theorem run_nxJd (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (hd ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions [.op .JUMPDEST]
      (CiosCachedTailDefs.nxJdState s mem pbi pb n hd ent dst ret rest) =
    some (CiosCachedTailDefs.nxState s mem pbi pb n hd ent dst ret rest) := by
  simp [runInstructions, Challenge.EvmProof.Stepper.runInstr,
    CiosCachedTailDefs.nxJdState, CiosCachedTailDefs.nxState, CiosCachedMacCore.framed,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  omega

/-- The dispatch on the multiply side, as a gas step. -/
def gasSteps_dispatchMul (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (hd ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hne : hd ≠ UInt256.ofNat 4777) :
    Challenge.EvmProof.GasSteps
      (CiosCachedTailDefs.exitState s mem pbi pb n hd ent dst ret rest)
      (CiosCachedTailDefs.nxJdState s mem pbi pb n hd ent dst ret rest) :=
  dispatchBlock.steps
    (environment (CiosCachedTailDefs.exitState s mem pbi pb n hd ent dst ret rest)
      hcode hfork hrun hnp) rfl
    (run_dispatchMul s mem pbi pb n hd ent dst ret rest hcap hne)

/-- The dispatch on the square side, as a gas step. -/
def gasSteps_dispatchSq (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (CiosCachedTailDefs.exitState s mem pbi pb n (UInt256.ofNat 4777) ent dst ret rest)
      (CiosCachedTailDefs.sqExitState s mem pbi pb n (UInt256.ofNat 4777) ent dst ret rest) :=
  dispatchBlock.steps
    (environment (CiosCachedTailDefs.exitState s mem pbi pb n (UInt256.ofNat 4777) ent dst ret rest)
      hcode hfork hrun hnp) rfl
    (run_dispatchSq s mem pbi pb n ent dst ret rest hcap hcode)

/-- The `nx` `JUMPDEST`, as a gas step. -/
def gasSteps_nxJd (s : State) (mem : ByteArray) (pbi : UInt256) (pb n : Nat)
    (hd ent dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (CiosCachedTailDefs.nxJdState s mem pbi pb n hd ent dst ret rest)
      (CiosCachedTailDefs.nxState s mem pbi pb n hd ent dst ret rest) :=
  nxJd.steps
    (environment (CiosCachedTailDefs.nxJdState s mem pbi pb n hd ent dst ret rest)
      hcode hfork hrun hnp) rfl
    (run_nxJd s mem pbi pb n hd ent dst ret rest hcap)

/-- The last row of a **square**: fall through the row loop's `JUMPI` into the dispatch,
which jumps to `sq_exit` with the frame retained. -/
def gasSteps_tailLastSq (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 4777).toNat = true) :
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pb n i (UInt256.ofNat 4777) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (CiosCachedTailDefs.sqExitState s (tailCarry mem c bi)
        (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n (UInt256.ofNat 4777) ent inv m0
        (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (tailLoop.steps (environment (tailState s mem c mu bi pb n i (UInt256.ofNat 4777) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CarryTailRows.run_last s mem c mu bi pb n i (UInt256.ofNat 4777) ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact hpb hpbFit hi (by rw [hcode]; exact hhd))).trans
  (gasSteps_dispatchSq { s with memory := tailCarry mem c bi } (tailCarry mem c bi)
    (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n ent inv m0
    (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hrun hcode hfork hnp)

/-- The last row: fall through the `JUMPI`, run the dispatch (`hd ≠ sq_row`, so it falls
through as well), drop the frame, jump to the CSUB guard (4658). -/
opaque gasSteps_tailLast (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = n)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hhd : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode hd.toNat = true)
    (hne : hd ≠ UInt256.ofNat 4777) :
    Challenge.EvmProof.GasSteps
      (tailState s mem c mu bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (tailCarry mem c bi) pdst ret rest) :=
  ((tailLoop.steps (environment (tailState s mem c mu bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CarryTailRows.run_last s mem c mu bi pb n i hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hact hpb hpbFit hi (by rw [hcode]; exact hhd))).trans
  ((gasSteps_dispatchMul { s with memory := tailCarry mem c bi } (tailCarry mem c bi)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hne).trans
    (gasSteps_nxJd { s with memory := tailCarry mem c bi } (tailCarry mem c bi)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n hd ent inv m0
      (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)
      (by simp only [List.length_cons]; omega) hrun hcode hfork hnp))).trans
  (exitBlock.steps (environment (CiosCachedTailDefs.nxState s (tailCarry mem c bi)
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) pb n hd ent inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) hcode hfork hrun hnp) rfl
    (CiosReadonly.run_exit { s with memory := tailCarry mem c bi }
      (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) hd
      (UInt256.ofNat (pb-32)) ent (l2Target n) tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap
      (by rw [hcode]; exact jumpDest4976)))

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

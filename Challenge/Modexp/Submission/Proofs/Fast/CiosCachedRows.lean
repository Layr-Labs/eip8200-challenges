import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Fixed-width cached CIOS row schedules

The dispatcher admits only four- and eight-limb inputs.  These certificates
spell out the fully unrolled schedules, leaving the arithmetic state in the
existing `Monpro` model.  There is no new arithmetic identity here.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

open CiosCached CiosCachedGas CiosCachedBlocks

opaque gasSteps_l1Four (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4604 s mem bi pa pb 4 i 0 pdst ret rest)
      (midState s (l1Step mem bi pa 4 4).memory
        (UInt256.ofNat (ptrAt (pa + 32 * 4 - 32) 3))
        (UInt256.ofNat (ptrAt (8224 + 32 * 4) 3))
        (l1Step mem bi pa 4 4).carry bi pa pb 4 i pdst ret rest) :=
  (gasSteps_l1Dispatch4 s mem bi pa pb i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Join s mem bi pa pb 4 i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4759 l1Mac4 s mem bi pa pb 4 i 0 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4796 l1Mac5 s mem bi pa pb 4 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4833 l1Mac6 s mem bi pa pb 4 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  gasSteps_l1Last s mem bi pa pb 4 i 3 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit

opaque gasSteps_l1Eight (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4604 s mem bi pa pb 8 i 0 pdst ret rest)
      (midState s (l1Step mem bi pa 8 8).memory
        (UInt256.ofNat (ptrAt (pa + 32 * 8 - 32) 7))
        (UInt256.ofNat (ptrAt (8224 + 32 * 8) 7))
        (l1Step mem bi pa 8 8).carry bi pa pb 8 i pdst ret rest) :=
  (gasSteps_l1Dispatch8 s mem bi pa pb i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4610 l1Mac0 s mem bi pa pb 8 i 0 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4647 l1Mac1 s mem bi pa pb 8 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4684 l1Mac2 s mem bi pa pb 8 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4721 l1Mac3 s mem bi pa pb 8 i 3 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Join s mem bi pa pb 8 i 4 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4759 l1Mac4 s mem bi pa pb 8 i 4 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4796 l1Mac5 s mem bi pa pb 8 i 5 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  (gasSteps_l1Mac 4833 l1Mac6 s mem bi pa pb 8 i 6 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit).trans <|
  gasSteps_l1Last s mem bi pa pb 8 i 7 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa hpaFit

opaque gasSteps_l2Four (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (l2At 4975 s mid bi mu c0 pa pb 4 i 0 pdst ret rest)
      (tailState s (l2Step mid mu c0 4 3).memory
        (UInt256.ofNat (ptrAt (32 * 4 - 64) 3))
        (UInt256.ofNat (ptrAt (8192 + 32 * 4) 3))
        (l2Step mid mu c0 4 3).carry mu bi pa pb 4 i pdst ret rest) :=
  (gasSteps_l2Dispatch4 s mid bi mu c0 pa pb i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l2Join s mid bi mu c0 pa pb 4 i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l2Mac 5142 64 l2Mac4 s mid bi mu c0 pa pb 4 i 0 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 5182 32 l2Mac5 s mid bi mu c0 pa pb 4 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  gasSteps_l2Mac 5222 0 l2Mac6 s mid bi mu c0 pa pb 4 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)

opaque gasSteps_l2Eight (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.GasSteps
      (l2At 4975 s mid bi mu c0 pa pb 8 i 0 pdst ret rest)
      (tailState s (l2Step mid mu c0 8 7).memory
        (UInt256.ofNat (ptrAt (32 * 8 - 64) 7))
        (UInt256.ofNat (ptrAt (8192 + 32 * 8) 7))
        (l2Step mid mu c0 8 7).carry mu bi pa pb 8 i pdst ret rest) :=
  (gasSteps_l2Dispatch8 s mid bi mu c0 pa pb i 0 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l2Mac 4981 192 l2Mac0 s mid bi mu c0 pa pb 8 i 0 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 5021 160 l2Mac1 s mid bi mu c0 pa pb 8 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 5061 128 l2Mac2 s mid bi mu c0 pa pb 8 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 5101 96 l2Mac3 s mid bi mu c0 pa pb 8 i 3 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Join s mid bi mu c0 pa pb 8 i 4 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l2Mac 5142 64 l2Mac4 s mid bi mu c0 pa pb 8 i 4 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 5182 32 l2Mac5 s mid bi mu c0 pa pb 8 i 5 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)).trans <|
  gasSteps_l2Mac 5222 0 l2Mac6 s mid bi mu c0 pa pb 8 i 6 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide)

/-- One complete four-limb row, stopping at the common tail block. -/
opaque gasSteps_rowFourToTail (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i pdst ret rest)
      (tailState s (rowL2 mem pa pb 4 i).memory
        (UInt256.ofNat (ptrAt (32 * 4 - 64) 3))
        (UInt256.ofNat (ptrAt (8192 + 32 * 4) 3))
        (rowL2 mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4)
        (rowBi mem pb 4 i) pa pb 4 i pdst ret rest) := by
  have hml4 : MachineState.readWord
      (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 9408 =
      UInt256.ofNat (32 * 4 - 32) :=
    (readWord_l1Step mem (rowBi mem pb 4 i) pa 4 9408 4 (by decide)
      (by omega)).trans hml
  have htl4 : MachineState.readWord
      (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 9440 =
      UInt256.ofNat (8224 + 32 * 4) :=
    (readWord_l1Step mem (rowBi mem pb 4 i) pa 4 9440 4 (by decide)
      (by omega)).trans htl
  refine (gasSteps_out s mem pa pb 4 i pdst ret rest hcap hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpa hpaFit hpb hpbFit hs32 htl).trans ?_
  refine (gasSteps_l1Four s mem (rowBi mem pb 4 i) pa pb i pdst ret rest hcap
    hrun hcode hfork hnp hact hpa hpaFit).trans ?_
  refine (gasSteps_mid s (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
    (UInt256.ofNat (ptrAt (pa + 32 * 4 - 32) 3))
    (UInt256.ofNat (ptrAt (8224 + 32 * 4) 3))
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry (rowBi mem pb 4 i)
    pa pb 4 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    (by decide) hml4 htl4).trans ?_
  simpa only [rowL1, rowMid, rowL2] using
    gasSteps_l2Four s
      (midMem (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
        (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry)
      (rowBi mem pb 4 i)
      (rowMu (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      (rowC0 (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      pa pb i pdst ret rest hcap hrun hcode hfork hnp hact

/-- One complete eight-limb row, stopping at the common tail block. -/
opaque gasSteps_rowEightToTail (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i pdst ret rest)
      (tailState s (rowL2 mem pa pb 8 i).memory
        (UInt256.ofNat (ptrAt (32 * 8 - 64) 7))
        (UInt256.ofNat (ptrAt (8192 + 32 * 8) 7))
        (rowL2 mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8)
        (rowBi mem pb 8 i) pa pb 8 i pdst ret rest) := by
  have hml8 : MachineState.readWord
      (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 9408 =
      UInt256.ofNat (32 * 8 - 32) :=
    (readWord_l1Step mem (rowBi mem pb 8 i) pa 8 9408 8 (by decide)
      (by omega)).trans hml
  have htl8 : MachineState.readWord
      (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 9440 =
      UInt256.ofNat (8224 + 32 * 8) :=
    (readWord_l1Step mem (rowBi mem pb 8 i) pa 8 9440 8 (by decide)
      (by omega)).trans htl
  refine (gasSteps_out s mem pa pb 8 i pdst ret rest hcap hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpa hpaFit hpb hpbFit hs32 htl).trans ?_
  refine (gasSteps_l1Eight s mem (rowBi mem pb 8 i) pa pb i pdst ret rest hcap
    hrun hcode hfork hnp hact hpa hpaFit).trans ?_
  refine (gasSteps_mid s (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
    (UInt256.ofNat (ptrAt (pa + 32 * 8 - 32) 7))
    (UInt256.ofNat (ptrAt (8224 + 32 * 8) 7))
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry (rowBi mem pb 8 i)
    pa pb 8 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    (by decide) hml8 htl8).trans ?_
  simpa only [rowL1, rowMid, rowL2] using
    gasSteps_l2Eight s
      (midMem (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
        (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry)
      (rowBi mem pb 8 i)
      (rowMu (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      (rowC0 (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      pa pb i pdst ret rest hcap hrun hcode hfork hnp hact

opaque gasSteps_rowFourNext (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 < 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i pdst ret rest)
      (outState s (rowMem mem pa pb 4 i) pa pb 4 (i + 1) pdst ret rest) :=
  (gasSteps_rowFourToTail s mem pa pb i pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
    by simpa only [rowMem] using
      gasSteps_tailNext s (rowL2 mem pa pb 4 i).memory
        (UInt256.ofNat (ptrAt (32 * 4 - 64) 3))
        (UInt256.ofNat (ptrAt (8192 + 32 * 4) 3))
        (rowL2 mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (rowBi mem pb 4 i)
        pa pb 4 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowFourLast (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i pdst ret rest)
      (mpCsubState s (rowMem mem pa pb 4 i) pdst ret rest) :=
  (gasSteps_rowFourToTail s mem pa pb i pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
    by simpa only [rowMem] using
      gasSteps_tailLast s (rowL2 mem pa pb 4 i).memory
        (UInt256.ofNat (ptrAt (32 * 4 - 64) 3))
        (UInt256.ofNat (ptrAt (8192 + 32 * 4) 3))
        (rowL2 mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (rowBi mem pb 4 i)
        pa pb 4 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowEightNext (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 < 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i pdst ret rest)
      (outState s (rowMem mem pa pb 8 i) pa pb 8 (i + 1) pdst ret rest) :=
  (gasSteps_rowEightToTail s mem pa pb i pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
    by simpa only [rowMem] using
      gasSteps_tailNext s (rowL2 mem pa pb 8 i).memory
        (UInt256.ofNat (ptrAt (32 * 8 - 64) 7))
        (UInt256.ofNat (ptrAt (8192 + 32 * 8) 7))
        (rowL2 mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (rowBi mem pb 8 i)
        pa pb 8 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowEightLast (s : State) (mem : ByteArray) (pa pb i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32)) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i pdst ret rest)
      (mpCsubState s (rowMem mem pa pb 8 i) pdst ret rest) :=
  (gasSteps_rowEightToTail s mem pa pb i pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa hpaFit hpb hpbFit hs32 htl hml).trans <|
    by simpa only [rowMem] using
      gasSteps_tailLast s (rowL2 mem pa pb 8 i).memory
        (UInt256.ofNat (ptrAt (32 * 8 - 64) 7))
        (UInt256.ofNat (ptrAt (8192 + 32 * 8) 7))
        (rowL2 mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (rowBi mem pb 8 i)
        pa pb 8 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRows

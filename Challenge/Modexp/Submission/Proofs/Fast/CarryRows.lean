import Challenge.Modexp.Submission.Proofs.Fast.CarryRowGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Fixed-width immediate-address CIOS row schedules

The dispatcher admits only four- and eight-limb inputs.  These certificates
spell out the fully unrolled schedules, leaving the arithmetic state in the
existing `Monpro` model.  There is no new arithmetic identity here.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

open CiosCached CarryRowGas CarryRowBlocks
open CiosCachedMidMemory CarryRowModel

private theorem extraCache_middleCarry {mem : ByteArray} {m96 m64 m32 : UInt256}
    (hc : CiosReadonlyExtra.ExtraCache mem m96 m64 m32) (c : UInt256) :
    CiosReadonlyExtra.ExtraCache (midMem1 mem c) m96 m64 m32 :=
  hc.of_preserved
    (readWord_midMem1 mem c 96 (Or.inl (by decide)))
    (readWord_midMem1 mem c 64 (Or.inl (by decide)))
    (readWord_midMem1 mem c 32 (Or.inl (by decide)))

opaque gasSteps_l1Four (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192) (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (l1At 4279 s mem bi pa pb 4 i 1 pdst ret rest)
      (midState s (l1Step mem bi pa 4 4).memory (l1Step mem bi pa 4 4).carry bi
        pa pb 4 i pdst ret rest) :=
  (gasSteps_l1Dispatch4 s mem bi pa pb i 1 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Join s mem bi pa pb 4 i 1 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4435 64 8320 l1Mac5 s mem bi pa pb 4 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Mac 4473 32 8288 l1Mac6 s mem bi pa pb 4 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  gasSteps_l1Last s mem bi pa pb 4 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa (by omega)

opaque gasSteps_l1Eight (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb i : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192) (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (l1At 4279 s mem bi pa pb 8 i 1 pdst ret rest)
      (midState s (l1Step mem bi pa 8 8).memory (l1Step mem bi pa 8 8).carry bi
        pa pb 8 i pdst ret rest) :=
  (gasSteps_l1Dispatch8 s mem bi pa pb i 1 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4282 192 8448 l1Mac1 s mem bi pa pb 8 i 1 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Mac 4320 160 8416 l1Mac2 s mem bi pa pb 8 i 2 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Mac 4358 128 8384 l1Mac3 s mem bi pa pb 8 i 3 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Mac 4396 96 8352 l1Mac4 s mem bi pa pb 8 i 4 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Join s mem bi pa pb 8 i 5 pdst ret rest hcap hrun hcode hfork hnp).trans <|
  (gasSteps_l1Mac 4435 64 8320 l1Mac5 s mem bi pa pb 8 i 5 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  (gasSteps_l1Mac 4473 32 8288 l1Mac6 s mem bi pa pb 8 i 6 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) hpa (by omega) hsnapshot).trans <|
  gasSteps_l1Last s mem bi pa pb 8 i pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) hpa (by omega)

opaque gasSteps_l2Four (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 4578 s mid bi mu c0 pa pb 4 i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 4 3).memory
        (l2Step mid mu c0 4 3).carry mu bi pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch4 s mid bi mu c0 pa pb i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_l2Join s mid bi mu c0 pa pb 4 i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_extraL2 1 4734 64 8320 8352 l2Mac4 s mid bi mu c0 pa pb 4 i 0 tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_extraL2 2 4768 32 8288 8320 l2Mac5 s mid bi mu c0 pa pb 4 i 1 tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2Final s mid bi mu c0 pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

opaque gasSteps_l2Eight (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb i : Nat) (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : CiosReadonlyExtra.ExtraCache mid m96 m64 m32) :
    Challenge.EvmProof.GasSteps
      (l2At 4578 s mid bi mu c0 pa pb 8 i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (l2Step mid mu c0 8 7).memory
        (l2Step mid mu c0 8 7).carry mu bi pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by
    simp only [List.length_cons]; omega
  exact (gasSteps_l2Dispatch8 s mid bi mu c0 pa pb i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_l2Mac 4581 11 192 8448 8480 l2Mac0 s mid bi mu c0 pa pb 8 i 0 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 4627 1 160 8416 8448 l2Mac1 s mid bi mu c0 pa pb 8 i 1 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_l2Mac 4663 1 128 8384 8416 l2Mac2 s mid bi mu c0 pa pb 8 i 2 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans <|
  (gasSteps_extraL2 0 4699 96 8352 8384 l2Mac3 s mid bi mu c0 pa pb 8 i 3 tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_l2Join s mid bi mu c0 pa pb 8 i 4 inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp).trans <|
  (gasSteps_extraL2 1 4734 64 8320 8352 l2Mac4 s mid bi mu c0 pa pb 8 i 4 tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  (gasSteps_extraL2 2 4768 32 8288 8320 l2Mac5 s mid bi mu c0 pa pb 8 i 5 tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc).trans <|
  gasSteps_l2Final s mid bi mu c0 pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp hact (by decide) (by decide)

/-- One complete four-limb row, stopping at the common tail block. -/
opaque gasSteps_rowFourToTail (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (rowL2Carry mem pa pb 4 i).memory
        (rowL2Carry mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4)
        (rowOverflow mem pa pb 4 i) pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by simp only [List.length_cons]; omega
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
  have hminv4 := inverse_l1Step mem (rowBi mem pb 4 i) pa 4 4 (by decide) hminv
  refine (gasSteps_out s mem pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpa (by omega) hpb hpbFit).trans ?_
  refine (gasSteps_commonFirst s mem (rowBi mem pb 4 i) pa pb 4 i
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
    (by decide) (by decide) (by omega) hc.lowAddress hAend).trans ?_
  refine (gasSteps_l1Four s mem (rowBi mem pb 4 i) pa pb i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
    hrun hcode hfork hnp hact hpa (by omega) hsnapshot).trans ?_
  refine (gasSteps_mid s (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
    (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry (rowBi mem pb 4 i)
    pa pb 4 i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    (by decide) hml4 htl4 hminv4 (hc.l1 (by decide) (rowBi mem pb 4 i) pa 4)).trans ?_
  simpa only [rowL1, rowMidCarry, rowL2Carry, rowOverflow] using
    gasSteps_l2Four s
      (midMem1 (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory
        (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry)
      (rowOverflow mem pa pb 4 i)
      (rowMu (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      (rowC0 (l1Step mem (rowBi mem pb 4 i) pa 4 4).memory 4)
      pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (extraCache_middleCarry (he.l1 (rowBi mem pb 4 i) pa 4 4 (by decide))
        (l1Step mem (rowBi mem pb 4 i) pa 4 4).carry)

/-- One complete eight-limb row, stopping at the common tail block. -/
opaque gasSteps_rowEightToTail (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i < 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (tailState s (rowL2Carry mem pa pb 8 i).memory
        (rowL2Carry mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8)
        (rowOverflow mem pa pb 8 i) pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) := by
  have hcap' : (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest).length ≤ 1005 := by simp only [List.length_cons]; omega
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
  have hminv8 := inverse_l1Step mem (rowBi mem pb 8 i) pa 8 8 (by decide) hminv
  refine (gasSteps_out s mem pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap' hrun hcode hfork hnp
    hact (by decide) (by decide) hi hpa (by omega) hpb hpbFit).trans ?_
  refine (gasSteps_commonFirst s mem (rowBi mem pb 8 i) pa pb 8 i
    tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
    (by decide) (by decide) (by omega) hc.lowAddress hAend).trans ?_
  refine (gasSteps_l1Eight s mem (rowBi mem pb 8 i) pa pb i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) hcap'
    hrun hcode hfork hnp hact hpa (by omega) hsnapshot).trans ?_
  refine (gasSteps_mid s (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
    (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry (rowBi mem pb 8 i)
    pa pb 8 i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
    (by decide) hml8 htl8 hminv8 (hc.l1 (by decide) (rowBi mem pb 8 i) pa 8)).trans ?_
  simpa only [rowL1, rowMidCarry, rowL2Carry, rowOverflow] using
    gasSteps_l2Eight s
      (midMem1 (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory
        (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry)
      (rowOverflow mem pa pb 8 i)
      (rowMu (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      (rowC0 (l1Step mem (rowBi mem pb 8 i) pa 8 8).memory 8)
      pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact
      (extraCache_middleCarry (he.l1 (rowBi mem pb 8 i) pa 8 8 (by decide))
        (l1Step mem (rowBi mem pb 8 i) pa 8 8).carry)

opaque gasSteps_rowFourNext (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 < 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (outState s (rowCarry mem pa pb 4 i) pa pb 4 (i + 1) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (gasSteps_rowFourToTail s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa (by omega) hpb hpbFit htl hml hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowCarry, rowOverflow] using
      gasSteps_tailNext s (rowL2Carry mem pa pb 4 i).memory
        (rowL2Carry mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (rowOverflow mem pa pb 4 i)
        pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowFourLast (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = 4)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 4 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 4 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 4))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 4))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 4 - 32))
    (hminv : inverseInvariant mem 4)
    (hc : CiosReadonly.ReadonlyCache mem 4 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*4-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 4) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 4 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowCarry mem pa pb 4 i) pdst ret rest) :=
  (gasSteps_rowFourToTail s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa (by omega) hpb hpbFit htl hml hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowCarry, rowOverflow] using
      gasSteps_tailLast s (rowL2Carry mem pa pb 4 i).memory
        (rowL2Carry mem pa pb 4 i).carry
        (rowMu (rowL1 mem pa pb 4 i).memory 4) (rowOverflow mem pa pb 4 i)
        pa pb 4 i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowEightNext (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 < 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (outState s (rowCarry mem pa pb 8 i) pa pb 8 (i + 1) inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest)) :=
  (gasSteps_rowEightToTail s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa (by omega) hpb hpbFit htl hml hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowCarry, rowOverflow] using
      gasSteps_tailNext s (rowL2Carry mem pa pb 8 i).memory
        (rowL2Carry mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (rowOverflow mem pa pb 8 i)
        pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest) (by simp only [List.length_cons]; omega) hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

opaque gasSteps_rowEightLast (s : State) (mem : ByteArray) (pa pb i : Nat)
    (tl inv m0 aEnd m96 m64 m32 pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hi : i + 1 = 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8)
    (hc : CiosReadonly.ReadonlyCache mem 8 tl inv m0)
    (he : CiosReadonlyExtra.ExtraCache mem m96 m64 m32)
    (hAend : aEnd = UInt256.ofNat (pa+32*8-32))
    (hsnapshot : StagedOperand.Snapshot mem pa 8) :
    Challenge.EvmProof.GasSteps
      (outState s mem pa pb 8 i inv m0 (tl :: m96 :: m64 :: m32 :: aEnd :: pdst :: ret :: rest))
      (mpCsubState s (rowCarry mem pa pb 8 i) pdst ret rest) :=
  (gasSteps_rowEightToTail s mem pa pb i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp
      hact (by omega) hpa (by omega) hpb hpbFit htl hml hminv hc he hAend hsnapshot).trans <|
    by simpa only [rowCarry, rowOverflow] using
      gasSteps_tailLast s (rowL2Carry mem pa pb 8 i).memory
        (rowL2Carry mem pa pb 8 i).carry
        (rowMu (rowL1 mem pa pb 8 i).memory 8) (rowOverflow mem pa pb 8 i)
        pa pb 8 i tl inv m0 aEnd m96 m64 m32 pdst ret rest hcap hrun hcode hfork hnp hact (by decide)
        hi hpb hpbFit

end Challenge.Modexp.Submission.Proofs.Fast.CarryRows

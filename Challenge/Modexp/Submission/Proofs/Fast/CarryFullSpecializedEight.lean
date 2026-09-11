import Challenge.Modexp.Submission.Proofs.Fast.CarryFullRowsEight

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open Challenge.Modexp.Submission.Proofs.Fast.CarryRows
open CarryRowModel CarryResult StagedOperand

/-- An eight-limb multiply: `mul entry` (pc 3920) → `common` → `setup` → the eight rows (row head
`hd = 4037`) → the final subtraction (pc 4667). -/
opaque gasSteps_specializedEight (L : RowLemmas) (E : EntryLemmas) (s : State) (mem : ByteArray)
    (pa pb : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * 8 ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * 8 ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * 8))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * 8))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * 8 - 32))
    (hminv : inverseInvariant mem 8) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (rowsCarry (mpZeroed s (stage mem pa 8) 8) pa pb 8 8) pdst ret rest) := by
  have hread (addr : Nat) (hd : addr+32 ≤ 8192 ∨ 9280 ≤ addr) :
      MachineState.readWord (stage mem pa 8) addr = MachineState.readWord mem addr :=
    read_stage_outside mem pa 8 addr (by omega)
  have hminv' : inverseInvariant (stage mem pa 8) 8 := by
    simpa only [inverseInvariant,
      hread (32*8-32) (Or.inl (by decide)),
      hread 9376 (Or.inr (by decide))] using hminv
  refine (E.gasSteps_mulEntry s mem pa pb pdst ret rest (by omega) hrun hcode hfork hnp).trans ?_
  refine (E.gasSteps_commonSetup s mem (UInt256.ofNat 4041) pa pb 8 pdst ret rest hcap hrun hcode
    hfork hnp hact (by decide) (by omega) hpb hpbFit hcds hs32 hml jumpDest_rowHead).trans ?_
  exact gasSteps_rowsEight L s (stage mem pa 8) pa pb
    (MachineState.readWord mem 9440) (MachineState.readWord mem 9376)
    (MachineState.readWord mem (32*8-32)) (UInt256.ofNat (pa+32*8-32))
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) pdst ret rest hcap hrun hcode hfork hnp hact
    hpaFit hpb hpbFit hminv'
    ⟨htl, (hread 9376 (Or.inr (by decide))).symm,
      (hread (32*8-32) (Or.inl (by decide))).symm⟩
    ⟨(hread 96 (Or.inl (by decide))).symm,
      (hread 64 (Or.inl (by decide))).symm,
      (hread 32 (Or.inl (by decide))).symm⟩ rfl
    (snapshot_stage mem pa 8 hpaFit)

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull

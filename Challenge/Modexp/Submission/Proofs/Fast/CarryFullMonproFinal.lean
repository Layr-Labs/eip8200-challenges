import Challenge.Modexp.Submission.Proofs.Fast.CarryFullMonproCsub
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowLemmas
import Challenge.Modexp.Submission.Proofs.Fast.CarryEntryLemmas

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

opaque gasSteps_monproFullOf (L : RowLemmas) (E : EntryLemmas) (s : State) (mem : ByteArray) (pa pb p : Nat)
    (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 9472)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (selectedRows (mpZeroed s (inputMemory mem pa (p+2)) (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) (p + 2)
        pdst ret rest) :=
  gasSteps_monproCsub L E s mem pa pb (p + 2) pdst ret rest (by omega) hrun hcode hfork hnp
    hact (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hminv hjump
    hdstFit
    (by
      let prepared := inputMemory mem pa (p+2)
      have ha' : Model.FastRepresents prepared pa (p+2) a :=
        (fastRepresents_inputMemory mem pa (p+2) pa (p+2) a hpaFit).2 ha
      have hb' : Model.FastRepresents prepared pb (p+2) b :=
        (fastRepresents_inputMemory mem pa (p+2) pb (p+2) b hpbFit).2 hb
      have hm' : Model.FastRepresents prepared 0 (p+2) mm :=
        (fastRepresents_inputMemory mem pa (p+2) 0 (p+2) mm (by omega)).2 hm
      have hminv' : ((MachineState.readWord prepared (32*(p+2)-32)).toNat *
          (MachineState.readWord prepared 9376).toNat + 1) % 2^256 = 0 := by
        simpa only [prepared,
          read_inputMemory_outside mem pa (p+2) (32*(p+2)-32) (Or.inl (by omega)),
          read_inputMemory_outside mem pa (p+2) 9376 (Or.inr (by decide))] using hminv
      have hr := selectedRows_agree (mpZeroed s prepared (p+2)) pa pb (p+2) (p+2)
        hpaFit hpbFit (by omega) hn32 (by omega)
      rw [CarryScratchAgreement.readWord_eq hr 8224 (Or.inr (by decide))]
      exact Monpro.monpro_tn_le_one s prepared pa pb p a b mm hn32 hpaFit hpbFit ha' hb' hm' ham
        hmpos hminv')

/-- **The sqCP1m multiply kernel** (`MonPro(pa, pb) → pdst`): from the `mul entry` (pc 3890) to the
return of the final subtraction, for every width (four and eight limbs through the kernel
rows, every other width through the generic `MONPRO`).  Statement unchanged from the base. -/
opaque gasSteps_monproFull (s : State) (mem : ByteArray) (pa pb p : Nat)
    (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 8192)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 9472)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 9376).toNat + 1) % 2 ^ 256 = 0) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (selectedRows (mpZeroed s (inputMemory mem pa (p+2)) (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) (p + 2)
        pdst ret rest) :=
  gasSteps_monproFullOf rowLemmas entryLemmas s mem pa pb p a b mm pdst ret rest hcap hrun hcode hfork hnp
    hact hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hjump hdstFit ha hb hm ham hmpos hminv

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull

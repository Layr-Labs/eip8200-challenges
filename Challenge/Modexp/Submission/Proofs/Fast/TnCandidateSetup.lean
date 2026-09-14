import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSetupEntry
import Challenge.Modexp.Submission.Proofs.Fast.TnCandidateArtifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSetup
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro StagedOperand TnCacheSetup

def block : Block TnCandidateArtifact.submissionArtifact .Osaka 3571 fullEntryProgram :=
  WindowTwentyOneSlice.block TnCandidateArtifact.allWellFormed 2662 59 3571 fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

noncomputable def setup_steps (s : State)
    (env : Environment TnCandidateArtifact.submissionArtifact .Osaka s)
    (mem : ByteArray) (hd : UInt256) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpaFit : pa+32*n ≤ 2816) (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 2816)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32*n-32))
    (htarget : Decode.isValidJumpDest s.executionEnv.code hd.toNat = true) :
    GasSteps (setupState s mem hd pa pb dst ret rest)
      (outState s (mpZeroed s (stage mem pa n) n) pb n 0 hd (l1Target n)
        (MachineState.readWord mem 2720) (MachineState.readWord mem (32*n-32))
        (MachineState.readWord mem 2784 :: MachineState.readWord mem 96 ::
          MachineState.readWord mem 64 :: MachineState.readWord mem 32 ::
          UInt256.ofNat (pa+32*n-32) :: dst :: ret :: rest)) :=
  block.steps (s := setupState s mem hd pa pb dst ret rest) (env.transfer rfl rfl) rfl
    (run_entry s mem hd pa pb n dst ret rest hcap hact hn hn32 hpaFit hpb hpbFit
      hcds hs32 hml htarget)

#print axioms setup_steps
end Challenge.Modexp.Submission.Proofs.Fast.TnCandidateSetup

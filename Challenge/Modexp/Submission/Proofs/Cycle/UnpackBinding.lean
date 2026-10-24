import Challenge.Modexp.Submission.Proofs.Cycle.Unpack
import Challenge.Modexp.Submission.Proofs.Cycle.FinalBlocks
set_option warningAsError true
namespace CycleSubmission.Unpack
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

noncomputable def gasSteps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8110, stack := SquareMeaning.frame0 inv a (fun _ => UInt256.ofNat 0) n rest}
      (result s inv a n rest) :=
  FinalBlocks.unpackFinalBlock.steps (env.transfer rfl rfl) rfl
    (run s inv a n rest hcap hact)

end CycleSubmission.Unpack

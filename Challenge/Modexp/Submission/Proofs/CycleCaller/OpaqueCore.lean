import Challenge.Modexp.Submission.Proofs.Cycle.Core
import Challenge.Modexp.Submission.Proofs.Cycle.EntryContract
import Challenge.Modexp.Submission.Proofs.Cycle.UnpackBinding
import Challenge.Modexp.Submission.Proofs.Cycle.Finish
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.CallerCore
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Model
open CycleSubmission.EntryMeaning CycleSubmission.InputWords CycleSubmission.WordArithmetic
open CycleSubmission.ControlArithmetic (value)

/-- Kernel-checked opacity boundary for callers composing the complete route. -/
noncomputable opaque run (s : State) (f : Caller) (k N A B x : Nat)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 943) (hact : 88 ≤ s.activeWords.toNat)
    (hcounter : f.counter = UInt256.ofNat (k-1))
    (hn : FastRepresents s.memory 0 8 N) (ha : FastRepresents s.memory 2368 8 A)
    (hb : FastRepresents s.memory 256 8 B)
    (hinv : (N*(MachineState.readWord s.memory 2720).toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hform : A ≡ x*2^2048 [MOD N]) (hAtop : A < 2^2048 - 2^1938) :
    Finish.Outcome {s with pc := UInt256.ofNat 5506, stack := saved f}
      (Precompile.natToBytes (B*x^(2^k)%N) 256) :=
  Core.run s f k N A B x hk hk16 env hcap hact hcounter hn ha hb hinv hN hodd hB hform hAtop

end CycleSubmission.CallerCore

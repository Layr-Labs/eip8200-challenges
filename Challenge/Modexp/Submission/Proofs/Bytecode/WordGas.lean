import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
import Challenge.EvmProof.Meter
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
# Exact gas use of the one-word MODEXP path

The path is value-independent.  Its only input-dependent loop counts are the
declared base and exponent byte lengths; the final memory expansion to
`0x1800` is included in the constant term.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordGas

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Word
open WordLoops
open WordExit
open WordCorrect

private theorem blockCost_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path,
      Challenge.EvmProof.Meter.CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work)
    (hactive : s.activeWords = t.activeWords) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s = work := by
  have hmeter := Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
    path work hresult hfork hfree hcost
  rw [hactive] at hmeter
  omega


@[simp] theorem gasSteps_baseSetup_cost (input : ByteArray) :
    (gasSteps_baseSetup input).cost = 5 := by
  have hmeter := blockCost_of_static baseSetupPath 5
    (run_baseSetup input) (by rfl)
    (by decide) (by rfl) (by rfl)
  unfold gasSteps_baseSetup
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter











def wordGas (input : ByteArray) : Nat :=
  969 + 140 * baseSize input + 1210 * exponentSize input



end Challenge.Modexp.Submission.Proofs.Bytecode.WordGas

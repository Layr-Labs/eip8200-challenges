import Challenge.EvmProof.Meter
import Challenge.Sha256.Submission.Proofs.Bytecode.Compression

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

def CopyFree : Instr → Prop
  | .op .CALLDATACOPY => False
  | .op .MCOPY => False
  | _ => True

private theorem noMemoryCost_eq_static (instruction : Instr) (s : State)
    (fork : Fork) (hfork : s.fork = fork) (hfree : CopyFree instruction) :
    Challenge.EvmProof.Meter.instrCostWithoutMemory instruction s =
      Challenge.EvmProof.Meter.instrStaticCost fork instruction := by
  cases instruction with
  | push width value =>
      simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
        Challenge.EvmProof.Meter.instrStaticCost, hfork]
  | op op =>
      cases op with
      | StopArith op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | CompBit op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Keccak op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Env op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Block op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | StackMemFlow op => cases op <;> simp [CopyFree,
          Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork] at hfree ⊢
      | Push op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Dup op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Swap op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | DupN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | SwapN op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Exchange op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | Log op => cases op; simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]
      | System op => cases op <;> simp [Challenge.EvmProof.Meter.instrCostWithoutMemory,
          Challenge.EvmProof.Meter.instrStaticCost, hfork]

private theorem blockCost_potential_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      Challenge.EvmProof.Meter.runLocatedBlockStaticCost path +
        MachineState.memCost t.activeWords.toNat := by
  apply Challenge.EvmProof.Meter.runLocatedBlock_cost_static_potential
    path hresult hfork
  intro located hmem q hq
  exact noMemoryCost_eq_static located.instruction q fork hq
    (hfree located hmem)

theorem blockCost_potential_of_static
    {artifact : Challenge.EvmProof.ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork)) {s t : State}
    (work : Nat)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hfork : s.fork = fork)
    (hfree : ∀ located ∈ path, CopyFree located.instruction)
    (hcost : Challenge.EvmProof.Meter.runLocatedBlockStaticCost path = work) :
    Challenge.EvmProof.Stepper.runLocatedBlockCost path s +
        MachineState.memCost s.activeWords.toNat =
      work + MachineState.memCost t.activeWords.toNat := by
  rw [blockCost_potential_static path hresult hfork hfree, hcost]

end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

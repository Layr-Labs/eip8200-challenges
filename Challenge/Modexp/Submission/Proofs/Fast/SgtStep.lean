import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option maxHeartbeats 8000000
set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Submission-local `SGT` step rule

The shared symbolic stepper `Challenge.EvmProof.Stepper.runInstr` has no `SGT`
case, so a straight-line block containing `SGT` cannot be run with
`runInstructions`.  This module lifts `EvmSemantics.EVM.StepRunning.sgt` into the
gas-parametric trace algebra through the public `Challenge.EvmProof.GasStep.of_running`
(exactly like the shared opcode wrappers in `Challenge.EvmProof.Ops`), and locates the
only `SGT` of the candidate bytecode: instruction 3739 at pc 4835 (0x126c) in the
square row `sq_row` (`JUMPDEST DUP1 MLOAD DUP1 SWAP15 PUSH0 SGT ...`).

Use: split `sq_row` at the `SGT` — a `Block` for idx 3566..3696 (pc 2464..2464),
`gasSteps_sqRowSgt`, then a `Block` for idx 3698..3840 (pc 4951..).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SgtStep

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

def gasStep_sgt {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SGT)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SGT
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.sgt (withGas s gas) a b rest hop hgas hstack hcap

theorem sqRowSgt_index : Artifact.submissionInstructions[4228]? = some (.op .SGT) := by
  rfl

theorem sqRowSgt_pc : Artifact.submissionArtifact.instructionPC 4228 = 5307 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem decodedOp_sqRowSgt (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 5307) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = Artifact.submissionArtifact.instructionPC 4228 := by
    rw [hpc, sqRowSgt_pc]; decide
  have hwf : Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Stepper.decodes_of_artifact Artifact.submissionArtifact s 4228 (.op .SGT)
    hcode hpcNat sqRowSgt_index hwf

theorem succ_4716 : (UInt256.ofNat 5307).succ = UInt256.ofNat 5308 := by
  decide

def gasSteps_sqRowSgt (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 5307)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 5308 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := gasStep_sgt (decodedOp_sqRowSgt s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_4716] at h
  exact h

def gasSteps_sqRowSgt_framed (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    GasSteps { t with pc := UInt256.ofNat 5307, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 5308, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_sqRowSgt { t with pc := UInt256.ofNat 5307, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.SgtStep

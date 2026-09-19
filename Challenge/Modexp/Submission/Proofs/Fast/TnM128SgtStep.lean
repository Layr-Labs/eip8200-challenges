import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact

set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Exact SGT rule for the eight-limb square row

The shared symbolic stepper has no SGT case. This module uses the operational
SGT rule and the gas-parametric trace algebra. In this runtime the square-row
SGT is instruction 3281 at pc 4324. The separate R4 path has its own SGT sites.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128SgtStep

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Gas-parametric `SGT` transition for any state whose decoder sees `SGT`. -/
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

/-- The SGT instruction in the eight-limb square row. -/
theorem sqRowSgt_index : TnM128CandidateArtifact.submissionInstructions[3394]? = some (.op .SGT) := by
  rfl

/-- Its exact byte address. -/
theorem sqRowSgt_pc : TnM128CandidateArtifact.submissionArtifact.instructionPC 3394 = 4274 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem decodedOp_sqRowSgt (s : State)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 4274) :
    s.decodedOp = some .SGT := by
  have hpcNat : s.pc.toNat = TnM128CandidateArtifact.submissionArtifact.instructionPC 3394 := by
    rw [hpc, sqRowSgt_pc]; decide
  have hwf : Stepper.WellFormed s.fork (.op .SGT) := by
    rw [hfork]
    exact ⟨by decide, trivial, rfl⟩
  exact Stepper.decodes_of_artifact TnM128CandidateArtifact.submissionArtifact s 3394 (.op .SGT)
    hcode hpcNat sqRowSgt_index hwf

theorem succ_4716 : (UInt256.ofNat 4274).succ = UInt256.ofNat 4275 := by
  decide

/-- The `SGT` of `sq_row` (pc 4099 → 4100): pops `a, b`, pushes `UInt256.sgt a b`.
In `sq_row` the operands are `a = 0` (from `PUSH0`) and `b = aprev`; see
`SquareDiag.sgt_zero_toNat` / `SquareModel.sgt_zero_eq_zero_of_lt`. -/
def gasSteps_sqRowSgt (s : State) (a b : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 4274)
    (hstack : s.stack = a :: b :: rest)
    (hcap : rest.length ≤ 1021)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := UInt256.ofNat 4275 } := by
  have hcap' : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := gasStep_sgt (decodedOp_sqRowSgt s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_4716] at h
  exact h

/-- Same rule for a state written as a record update of a template
(`{ t with pc := 4099, stack := a :: b :: rest, memory := m }`), the form used by
the kernel frames. -/
def gasSteps_sqRowSgt_framed (t : State) (m : ByteArray) (a b : UInt256)
    (rest : List UInt256)
    (hcode : t.executionEnv.code = TnM128Candidate.bytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1021)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    GasSteps { t with pc := UInt256.ofNat 4274, stack := a :: b :: rest, memory := m }
      { t with pc := UInt256.ofNat 4275, stack := UInt256.sgt a b :: rest, memory := m } :=
  gasSteps_sqRowSgt { t with pc := UInt256.ofNat 4274, stack := a :: b :: rest, memory := m }
    a b rest hcode hfork rfl rfl hcap hrun hnp

end Challenge.Modexp.Submission.Proofs.Fast.TnM128SgtStep

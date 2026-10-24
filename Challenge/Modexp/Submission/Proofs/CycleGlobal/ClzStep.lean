import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option maxHeartbeats 8000000
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000

/-!
# Submission-local `CLZ` step rule

The shared symbolic stepper `Challenge.EvmProof.Stepper.runInstr` has no `CLZ`
case, so a straight-line block containing `CLZ` cannot be run with
`runLocatedBlock`.  This module lifts the relational rule
`EvmSemantics.EVM.StepRunning.clz` into the gas-parametric trace algebra through the
public `Challenge.EvmProof.GasStep.of_running`, exactly as `SgtStep` does for `SGT`,
and locates the only `CLZ` of the candidate bytecode: instruction 2091 at pc 2672
(0x0a70) in the estimator prologue (`... DUP1 CLZ DUP1 NOT PUSH0 SUB PUSH2 0640 MSTORE`).

Use: split the prologue block at the `CLZ`: a located block for idx 2077..2090
(pc 2658..2671), `gasSteps_clz`, then a located block for idx 2092..2114 (pc 2673..).
-/

namespace CycleSubmission.Global.Fast.ClzStep
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast


open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Gas-parametric `CLZ` transition for any state whose decoder sees `CLZ`. -/
def gasStep_clz {s : State} {a : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .CLZ)
    (hstack : s.stack = a :: rest)
    (hcap : s.stack.length + Operation.pushArity .CLZ ≤
      1024 + Operation.popArity .CLZ)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.clz a :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .CLZ
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.clz (withGas s gas) a rest hop hgas hstack hcap

/-- The candidate's only `CLZ` is instruction 2091. -/
theorem clz_index : CycleSubmission.Artifact.instructions[1951]? = some (.op .CLZ) := by
  rfl

/-- ... at program counter 2672 (0x0a70). -/
theorem clz_pc : CycleSubmission.Artifact.artifact.instructionPC 1951 = 2502 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

theorem decodedOp_clz (s : State)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hpc : s.pc = UInt256.ofNat 2502) :
    s.decodedOp = some .CLZ := by
  have hpcNat : s.pc.toNat = CycleSubmission.Artifact.artifact.instructionPC 1951 := by
    rw [hpc, clz_pc]; decide
  have hwf : Stepper.WellFormed s.fork (.op .CLZ) := by
    rw [hfork]
    exact ⟨by decide, trivial, by decide⟩
  exact Stepper.decodes_of_artifact CycleSubmission.Artifact.artifact s 1951 (.op .CLZ)
    hcode hpcNat clz_index hwf

theorem succ_2672 : (UInt256.ofNat 2502).succ = UInt256.ofNat 2503 := by
  decide

/-- The `CLZ` of the estimator prologue (pc 2672 → 2673): pops `a`, pushes `UInt256.clz a`.
There `a = L`, the lowest set bit of the modulus top limb; see `Shift.clz_two_pow`. -/
def gasSteps_clz (s : State) (a : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka)
    (hpc : s.pc = UInt256.ofNat 2502)
    (hstack : s.stack = a :: rest)
    (hcap : rest.length ≤ 1023)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.clz a :: rest, pc := UInt256.ofNat 2503 } := by
  have hcap' : s.stack.length + Operation.pushArity .CLZ ≤
      1024 + Operation.popArity .CLZ := by
    rw [hstack]
    simp only [List.length_cons]
    simp only [Operation.pushArity, Operation.popArity]
    omega
  have h := gasStep_clz (decodedOp_clz s hcode hfork hpc) hstack hcap' hrun hnp
  rw [hpc, succ_2672] at h
  exact h

/-- Same rule for a state written as a record update of a carrier
(`{ t with pc := 2502, stack := a :: rest, memory := m }`), the form of the shift-reduce
states. -/
def gasSteps_clz_framed (t : State) (m : ByteArray) (a : UInt256) (rest : List UInt256)
    (hcode : t.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : t.fork = .Osaka)
    (hcap : rest.length ≤ 1023)
    (hrun : t.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig t.executionEnv.precompileConfig t.executionEnv.fork
      t.executionEnv.codeAddr = false) :
    GasSteps { t with pc := UInt256.ofNat 2502, stack := a :: rest, memory := m }
      { t with pc := UInt256.ofNat 2503, stack := UInt256.clz a :: rest, memory := m } :=
  gasSteps_clz { t with pc := UInt256.ofNat 2502, stack := a :: rest, memory := m }
    a rest hcode hfork rfl rfl hcap hrun hnp

end CycleSubmission.Global.Fast.ClzStep

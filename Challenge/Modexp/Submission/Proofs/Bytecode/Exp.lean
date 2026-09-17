import Challenge.EvmProof.Ops

set_option warningAsError true
set_option maxRecDepth 4000000
-- `UInt256.exp` is `a.toNat ^ b.toNat % size`; the elaborator refuses to evaluate a
-- `^` whose exponent exceeds 256 unless this is raised.  With `warningAsError` on,
-- leaving it out is a hard build error rather than a silent `sorryAx`.
set_option exponentiation.threshold 200000

/-! A gas-accounted rule for `EXP`.

The generic straight-line evaluator does not expose this opcode, so the
submission proves the corresponding EVM step directly through the shared
gas-step interface, exactly as it already does for `MSIZE`.  `EXP` is the only
instruction in the appended fixed-vector block that the evaluator does not
handle, and it occurs once, between two blocks it handles completely.

`exp_three_ffff` is the arithmetic fact the memoised value rests on.  The
exponent is two bytes, so the dynamic charge is a closed constant and the whole
instruction costs `10 + 50 * 2 = 110`. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Exp

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

def step {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .EXP)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .EXP ≤
      1024 + Operation.popArity .EXP)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.exp a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .EXP + Gas.expByteCost s.fork b
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  -- `StepRunning.exp` charges the base and the per-byte cost in two subtractions;
  -- `of_running` expects one subtraction of their sum.
  simpa [withGas, cost, Nat.sub_sub] using
    StepRunning.exp (withGas s gas) a b rest hop hgas hstack hcap

@[simp] theorem step_cost {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .EXP)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .EXP ≤
      1024 + Operation.popArity .EXP)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (step hop hstack hcap hrun hnp).cost
      = Gas.baseCost s.fork .EXP + Gas.expByteCost s.fork b := rfl

/-- The dynamic charge for the two-byte exponent `0xffff`. -/
theorem expByteCost_ffff :
    Gas.expByteCost .Osaka (UInt256.ofNat 65535) = 100 := by
  decide

/-- `3 ^ 65535 mod 2^256`.  The top bit of the result is clear, so this value is
also `3 ^ 65535 mod 2^255`, which is what the memoised tuple's modulus asks for. -/
theorem exp_three_ffff :
    UInt256.exp (UInt256.ofNat 3) (UInt256.ofNat 65535) =
      UInt256.ofNat
        0x3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Exp

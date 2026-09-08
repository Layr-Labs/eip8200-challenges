import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge0
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeBridge4
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeOdd2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundCertificate

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open PackedStep0 PackedStepFrame PackedEmit PackedTemplateGeneric PackedBridge
open PackedRunOpBridge

theorem emitted_constant (group : Nat) :
    packedK group = PackedSpreadSchedule.groupConstant group := rfl

def even0Ops (lo hi sl sr : Nat) : List Op :=
  pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
    bodyEven0 (shiftSupply (32 - sl)) (shiftSupply (32 - sr))

/-- A parameterized group-0 even round now has a gas-parametric semantic trace.
The remaining site-specific obligation is its located plan, not arithmetic. -/
theorem even0_gas {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork))
    (s : State) (lo hi sl sr : Nat) (a b c d e : UInt256)
    (sf : Suffix) (rest : List UInt256)
    (hstd : FrameStd sf) (hshift : SuffixStd sf)
    (hstack : s.stack = frameStack ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩ ++ rest)
    (plan : LocatedPlan (even0Ops lo hi sl sr) path s)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, Challenge.EvmProof.Stepper.runLocatedBlock path s = some t ∧
      ∃ _trace : Challenge.EvmProof.GasSteps s t,
        t.stack = frameStack
          (stepFrame 0 sl sr
            (memoryWord s (UInt256.ofNat lo) ||| memoryWord s (UInt256.ofNat hi))
            ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩) ++ rest ∧ t.memory = s.memory := by
  apply gasSteps_of_runOps plan hcode hfork hrun hnp
  rw [hstack]
  exact PackedProbeBridge0.bodyEven0_stepFrame (memoryWord s) lo hi sl sr
    a b c d e sf rest hstd hshift

def evenOps (group lo hi sl sr : Nat) : List Op :=
  pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
    (match group with
    | 0 => bodyEven0
    | 1 => bodyEven1
    | 2 => bodyEven2
    | 3 => bodyEven3
    | _ => bodyEven4) (shiftSupply (32 - sl)) (shiftSupply (32 - sr))

/-- Uniform abstract execution for all five even classes, retaining the group bound. -/
theorem even_exec (group : Nat) (hg : group < 5)
    (memAt : UInt256 → UInt256) (lo hi sl sr : Nat)
    (a b c d e : UInt256) (sf : Suffix) (rest : List UInt256)
    (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    runOps memAt (evenOps group lo hi sl sr)
      (frameStack ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩ ++ rest)
      = some (frameStack
        (stepFrame group sl sr
          (memAt (UInt256.ofNat lo) ||| memAt (UInt256.ofNat hi))
          ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩) ++ rest) := by
  have hcases : group = 0 ∨ group = 1 ∨ group = 2 ∨ group = 3 ∨ group = 4 := by omega
  rcases hcases with h | h | h | h | h
  · subst group
    exact PackedProbeBridge0.bodyEven0_stepFrame memAt lo hi sl sr
      a b c d e sf rest hstd hshift
  · subst group
    exact PackedProbeBridge1.bodyEven1_stepFrame memAt lo hi sl sr
      a b c d e sf rest hstd hshift
  · subst group
    exact PackedProbeBridge2.bodyEven2_stepFrame memAt lo hi sl sr
      a b c d e sf rest hstd hshift
  · subst group
    exact PackedProbeBridge3.bodyEven3_stepFrame memAt lo hi sl sr
      a b c d e sf rest hstd hshift
  · subst group
    exact PackedProbeBridge4.bodyEven4_stepFrame memAt lo hi sl sr
      a b c d e sf rest hstd hshift

/-- All even classes lift to actual gas-parametric traces under a located plan. -/
theorem evenOps_emitRound (i : Nat) :
    evenOps (i / 16) (16 * Crypto.Ripemd160.r[i]!)
      (16 * Crypto.Ripemd160.rP[i]! + 8)
      Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
      = emitRound Phase.even i := by
  unfold evenOps emitRound loadPrefix roundBody
  generalize i / 16 = g
  rcases g with _ | (_ | (_ | (_ | g))) <;> rfl

/-- The real table-driven emitter, not an independent opcode schedule. -/
theorem emitted_even_exec (i : Nat) (hi : i < 80)
    (memAt : UInt256 → UInt256) (a b c d e : UInt256)
    (sf : Suffix) (rest : List UInt256)
    (hstd : FrameStd sf) (hshift : SuffixStd sf) :
    runOps memAt (emitRound Phase.even i)
      (frameStack ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩ ++ rest)
      = some (frameStack
        (stepFrame (i / 16) Crypto.Ripemd160.s[i]! Crypto.Ripemd160.sP[i]!
          (memAt (UInt256.ofNat (16 * Crypto.Ripemd160.r[i]!)) |||
            memAt (UInt256.ofNat (16 * Crypto.Ripemd160.rP[i]! + 8)))
          ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩) ++ rest) := by
  rw [← evenOps_emitRound]
  exact even_exec (i / 16) (by omega) memAt _ _ _ _ a b c d e sf rest hstd hshift

/-- All even classes lift to actual gas-parametric traces under a located plan. -/
theorem even_gas {artifact : ProgramArtifact} {fork : Fork}
    (group : Nat) (hg : group < 5)
    (path : List (Challenge.EvmProof.Stepper.Located artifact fork))
    (s : State) (lo hi sl sr : Nat) (a b c d e : UInt256)
    (sf : Suffix) (rest : List UInt256)
    (hstd : FrameStd sf) (hshift : SuffixStd sf)
    (hstack : s.stack = frameStack ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩ ++ rest)
    (plan : LocatedPlan (evenOps group lo hi sl sr) path s)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, Challenge.EvmProof.Stepper.runLocatedBlock path s = some t ∧
      ∃ _trace : Challenge.EvmProof.GasSteps s t,
        t.stack = frameStack
          (stepFrame group sl sr
            (memoryWord s (UInt256.ofNat lo) ||| memoryWord s (UInt256.ofNat hi))
            ⟨⟨a, b, c, d, e⟩, sf, Phase.even⟩) ++ rest ∧ t.memory = s.memory := by
  apply gasSteps_of_runOps plan hcode hfork hrun hnp
  rw [hstack]
  exact even_exec group hg (memoryWord s) lo hi sl sr a b c d e sf rest hstd hshift

#print axioms even_exec
#print axioms evenOps_emitRound
#print axioms emitted_even_exec
#print axioms even_gas

#print axioms emitted_constant
#print axioms even0_gas
#print axioms PackedHashEntry.compress_model

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundCertificate

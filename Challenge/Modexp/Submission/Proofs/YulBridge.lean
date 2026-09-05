import Challenge.Modexp.Spec
import Challenge.Modexp.ProofSupport.InitialState
import YulEvmCompiler.Correctness

set_option warningAsError true

/-!
# From a Yul-level obligation to the MODEXP challenge statement

For any program accepted by the verified compiler, the bytecode challenge can
be discharged by proving two source-level facts: that the Yul program returns
the MODEXP precompile result, and that a fresh Yul state abstracts the fixed
EVM initial state.  This mirrors `Challenge/Ripemd160/ProofSupport/Yul.lean`
and contains no MODEXP-specific arithmetic: the entire algorithm obligation is
`ComputesSpec`.
-/

namespace Challenge.Modexp.Submission.Proofs.YulBridge

open EvmSemantics
open EvmSemantics.EVM
open YulSemantics (Block Run VEnv)
open YulSemantics.EVM (EvmState Op evmWithExternal ExternalCalls ExternalCreates)
open YulEvmCompiler

/-- The MODEXP precompile result at the byte-list view used by Yul
semantics. -/
def specOf (calldata : List UInt8) : List UInt8 :=
  (Challenge.Modexp.spec (mkCode calldata)).toList

/-- The reference implementation neither calls contracts nor creates them. -/
@[reducible] def localModel : ExternalModel :=
  { calls := ExternalCalls.none, creates := ExternalCreates.none }

/-- The gas-free source dialect used by the functional obligation. -/
abbrev localDialect := evmWithExternal ExternalCalls.none ExternalCreates.none

/-- A target initial state is represented by a fresh Yul state carrying the
same calldata. `StateMatch` is gas-independent, so one source state suffices
for every target gas budget. -/
def AbstractsInitialState (code : ByteArray) : Prop :=
  ∀ calldata : ByteArray, ∃ yst : EvmState,
    (∀ g : Nat, StateMatch yst (Challenge.Modexp.initialState code calldata g)) ∧
    yst.memory = (fun _ => 0) ∧
    yst.env.calldata = calldata.toList ∧
    yst.halted = none

/-- From any fresh source state, the program returns the MODEXP precompile
result for its calldata. -/
def ComputesSpec (prog : Block Op) : Prop :=
  ∀ yst : EvmState, yst.memory = (fun _ => 0) → yst.halted = none →
    ∃ (V : VEnv localDialect) (yst' : EvmState),
      Run localDialect prog yst V yst' .halt ∧
        yst'.halted = some (.ret, specOf yst.env.calldata)

theorem initialState_pc (code calldata : ByteArray) (gas : Nat) :
    (Challenge.Modexp.initialState code calldata gas).pc = UInt256.ofNat 0 := rfl

theorem initialState_stack (code calldata : ByteArray) (gas : Nat) :
    (Challenge.Modexp.initialState code calldata gas).stack = [] := rfl

theorem initialState_gas (code calldata : ByteArray) (gas : Nat) :
    (Challenge.Modexp.initialState code calldata gas).gasAvailable = gas := rfl

/-- The challenge's fixed initial state meets the verified compiler theorem's
target-side frame conditions. -/
theorem initialState_frameOK {code calldata : ByteArray} {gas : Nat}
    (hsize : code.size < 2 ^ 256) :
    FrameOK code (Challenge.Modexp.initialState code calldata gas) where
  hcode := rfl
  codeSmall := hsize
  fork := rfl
  noPrecompile := deployAddress_not_precompile
  callStack := rfl
  running := rfl

/-- A source-level MODEXP proof, together with the verified compiler theorem,
implies the bytecode challenge statement. -/
theorem correct_of_computesSpec {prog : Block Op} {is : List Instr}
    (hcomp : compile prog = some is)
    (hsize : (assemble is).size < 2 ^ 256)
    (habs : AbstractsInitialState (assemble is))
    (hyul : ComputesSpec prog) :
    Challenge.Modexp.Correct (assemble is) := by
  intro calldata _hfit
  obtain ⟨yst, hmatch, hmem, hcd, hhalted⟩ := habs calldata
  obtain ⟨V, yst', hrun, hres⟩ := hyul yst hmem hhalted
  obtain ⟨b, H⟩ :=
    compile_correct_eval (model := localModel) ExternalsRealized.none hcomp
      hrun
  refine ⟨b, fun g hg => ?_⟩
  obtain ⟨-, hhalt⟩ :=
    H (Challenge.Modexp.initialState (assemble is) calldata g)
      (initialState_frameOK hsize) (hmatch g)
      (initialState_pc _ _ _) (initialState_stack _ _ _)
      (by rw [initialState_gas]; exact hg)
  obtain ⟨hk, hyk, heval⟩ := hhalt rfl
  rw [hres] at hyk
  cases hyk
  simpa [resultOf, specOf, hcd, mkCode_toList, Challenge.Modexp.spec] using heval

end Challenge.Modexp.Submission.Proofs.YulBridge

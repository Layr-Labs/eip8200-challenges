import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Local20261028.FirstCopy
import Challenge.Ripemd160.Submission.Local20261028.Return32SerializeMath
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstComplete
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open FirstEntry

def prepared (s : State) (input : ByteArray) : State :=
  FirstCore.prepared (FirstRead.result (high (FirstCopy.copied s input)))
def resultHash (s : State) (input : ByteArray) : Compression.HashState :=
  CoreFunctional.result (prepared s input).memory FirstCore.initialHash
def result (s : State) (input : ByteArray) (rho : List UInt256) : State :=
  Return32Serialize.result (prepared s input) (resultHash s input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (NormalPrepare.masks rho)

theorem load_eq (input : ByteArray) (h32 : input.size = 32) :
    MachineState.readWord input 0 =
      MachineState.readWord (PairedScheduleMemory.writeWord (FirstSpec.copiedMemory input) 162
        FirstInitial.highWord) 1056 := by
  rw [PairedScheduleMemory.read_writeWord_disjoint _ _ _ _ (Or.inr (by decide : 162+32 ≤ 1056))]
  unfold MachineState.readWord FirstSpec.copiedMemory
  rw [← h32, Memory.readPadded_zero_size, Memory.readPadded_writeBytes_same]

def gasSteps (s : State) (e : Env s) (input : ByteArray) (rho : List UInt256)
    (hs : rho.length ≤ 880) (hcal : s.executionEnv.calldata = input) (h32 : input.size = 32)
    (hm : MachineState.writeBytes s.memory input 1056 = FirstSpec.copiedMemory input)
    (ha : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 1056 32) = UInt256.ofNat 34) :
    GasSteps {s with pc := UInt256.ofNat 245, stack := rho} (result s input rho) := by
  have ge := FirstCopy.entry s e input rho hs hcal h32 hm ha
  have gc := FirstReadGas.complete (high (FirstCopy.copied s input)) (UInt256.ofNat 9949) rho
    (by omega) e.running (by change (34 : Nat) ≤ 34; decide) e.code e.fork e.noPrecompile
    (by change MachineState.readWord s.executionEnv.calldata 0 = MachineState.readWord
          (PairedScheduleMemory.writeWord (FirstSpec.copiedMemory input) 162 FirstInitial.highWord) 1056
        rw [hcal]; exact load_eq input h32)
  have ep : Env (prepared s input) := ⟨e.code,e.fork,e.running,e.noPrecompile⟩
  have gd := dispatch (prepared s input) ep (resultHash s input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (NormalPrepare.masks rho)
    (by simp [NormalPrepare.masks]; omega)
  have go := Return32Serialize.gasSteps (prepared s input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (resultHash s input) rho (by omega)
    e.running e.code e.fork e.noPrecompile (by change s.executionEnv.calldata.size = 32; rw [hcal,h32])
  exact ge.trans (gc.trans (gd.trans go))

theorem returned_spec (s : State) (input : ByteArray) (rho : List UInt256)
    (h32 : input.size = 32) : (result s input rho).hReturn = spec input := by
  apply Return32Serialize.returned_spec_of_hashArray
  exact FirstMessageSpec.hash_spec (high (FirstCopy.copied s input)) input h32 rfl

theorem eval_of_returned_trace (s t : State) (output : ByteArray)
    (trace : GasSteps s t) (hr : t.halt = .Returned) (hc : t.callStack = [])
    (hb : t.hReturn = output) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (withGas s gas) (.returned output) := by
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have he := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hc, hr])
  rw [State.toResult_returned _ (by exact hr)] at he
  change Eval (withGas s gas) (.returned t.hReturn) at he
  rw [hb] at he
  exact he

/-- Full generic path for arbitrary 32-byte calldata, with a bounded leftover stack. -/
theorem correct_from_entry (input : ByteArray) (rho : List UInt256) (hs : rho.length ≤ 880)
    (h32 : input.size = 32)
    (prefixTrace : GasSteps (initialState Benchmark.bytecode input 0)
      {initialState Benchmark.bytecode input 0 with pc := UInt256.ofNat 245, stack := rho}) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState Benchmark.bytecode input gas) (.returned (spec input)) := by
  let s := initialState Benchmark.bytecode input 0
  have e : Env s := ⟨rfl,rfl,rfl,deployAddress_not_precompile⟩
  have gt := prefixTrace.trans (gasSteps s e input rho hs rfl h32 rfl rfl)
  obtain ⟨g₀,hg⟩ := eval_of_returned_trace (initialState Benchmark.bytecode input 0)
    (result s input rho) (spec input) gt rfl rfl (returned_spec s input rho h32)
  exact ⟨g₀,fun gas hgas => hg gas hgas⟩
#print axioms load_eq
#print axioms gasSteps
#print axioms returned_spec
#print axioms correct_from_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstComplete

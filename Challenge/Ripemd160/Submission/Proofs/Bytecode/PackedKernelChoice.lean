import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashInjectivity
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

set_option warningAsError true
set_option autoImplicit false

/-!
# Total packed block kernel from a valid-machine endpoint witness

The packed trace naturally produces an endpoint only when the calldata,
block context, code, fork, running state, and precompile conditions hold.  A
`StackRunBridge.BlockKernel`, however, names a total next-state function and
states its mathematical result independently of the machine conditions.

This module bridges that interface without asserting an exact record for the
packed trace.  On a valid machine it chooses the witnessed packed endpoint.
Otherwise it writes the mathematical result with the proved ascending
five-word combine-store model.  The invalid branch can never be selected by
`BlockKernel.gasSteps`, while its unconditional hash and frame properties make
the total function sound.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedKernelChoice

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

/-- Exactly the premises under which a concrete packed block trace is needed. -/
structure ValidMachineContext (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) : Prop where
  fits : CalldataFits input
  blockIndex : i < DriverTrace.blockCount input
  blockContext : StackRunBridge.BlockContext s input i h
  code : s.executionEnv.code = submissionBytecode
  fork : s.fork = .Osaka
  running : s.halt = .Running
  noPrecompile : Precompile.isPrecompileWithConfig
    s.executionEnv.precompileConfig s.executionEnv.fork
    s.executionEnv.codeAddr = false

/-- The endpoint facts the concrete packed body-and-tail proof must expose.
No exact-record equality and no exact active-memory formula is required. -/
structure ValidEndpoint (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (t : State) : Prop where
  executionEnv : t.executionEnv = s.executionEnv
  halt : t.halt = s.halt
  callStack : t.callStack = s.callStack
  wordAbove : ∀ address, 0x200 ≤ address →
    StackRunBridge.wordAt t address = StackRunBridge.wordAt s address
  hashResult : (CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input i) →
    StackRunBridge.hashAt32 t =
    StackRunBridge.embedHashArray
      (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
        (Padding.paddedMessage input) (DriverTrace.blockOffset i))
  gasSteps : Nonempty (GasSteps (DriverTrace.dispatchEntry s input i)
    (DriverTrace.compressReturned t input i))

/-- The sole concrete input to the totalization layer. -/
def EndpointProvider : Prop :=
  ∀ (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState),
    ValidMachineContext s input i h →
      ∃ t, ValidEndpoint s input i h t

/-- The total endpoint contract is field-for-field the existing
`StackRunBridge.BlockKernel` contract. -/
structure EndpointSpec (s : State) (input : ByteArray) (i : Nat)
    (t : State) : Prop where
  executionEnv : t.executionEnv = s.executionEnv
  halt : t.halt = s.halt
  callStack : t.callStack = s.callStack
  wordAbove : ∀ address, 0x200 ≤ address →
    StackRunBridge.wordAt t address = StackRunBridge.wordAt s address
  hashResult : ∀ (h : Compression.HashState) (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input)
    (_ctx : StackRunBridge.BlockContext s input i h)
    (_hmodel : CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input i),
    StackRunBridge.hashAt32 t =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i))
  gasSteps : ∀ (h : Compression.HashState) (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input)
    (_ctx : StackRunBridge.BlockContext s input i h)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (_hfork : s.fork = .Osaka) (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig
      s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false),
    Nonempty (GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned t input i))

/-- A valid packed witness determines a unique mathematical hash result even
if a caller supplies a differently named `HashState`: both are embedded as
the same five incoming memory words. -/
private theorem validEndpoint_hashResult_all
    {s : State} {input : ByteArray} {i : Nat}
    {chosen supplied : Compression.HashState} {t : State}
    (hvalid : ValidMachineContext s input i chosen)
    (hendpoint : ValidEndpoint s input i chosen t)
    (ctx : StackRunBridge.BlockContext s input i supplied)
    (hmodel : CompressionCorrect.hashArray supplied =
      CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 t =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock
          (CompressionCorrect.hashArray supplied)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  have hembed : Compression.embedHash supplied =
      Compression.embedHash chosen :=
    ctx.hash.symm.trans hvalid.blockContext.hash
  have hsame : supplied = chosen :=
    PackedHashInjectivity.embedHash_injective hembed
  subst supplied
  exact hendpoint.hashResult hmodel

/-- Mathematical output selected only when the concrete machine premises do
not hold.  Its incoming hash is decoded from the five current chaining words,
so the state is independent of any externally supplied proof witness. -/
def fallbackOutput (s : State) (input : ByteArray) (i : Nat) :
    Compression.EvmHashState :=
  StackRunBridge.embedHashArray
    (Crypto.Ripemd160.compressBlock
      (CompressionCorrect.hashArray
        (PackedHashInjectivity.decode (StackRunBridge.hashAt32 s)))
      (Padding.paddedMessage input) (DriverTrace.blockOffset i))

def fallbackState (s : State) (input : ByteArray) (i : Nat) : State :=
  let output := fallbackOutput s input i
  { s with memory := (PackedCombineMemory.writeHash s.memory
      output.h0 output.h1 output.h2 output.h3 output.h4) }

@[simp] theorem fallbackState_memory (s : State) (input : ByteArray) (i : Nat) :
    (fallbackState s input i).memory =
      PackedCombineMemory.writeHash s.memory
        (fallbackOutput s input i).h0 (fallbackOutput s input i).h1
        (fallbackOutput s input i).h2 (fallbackOutput s input i).h3
        (fallbackOutput s input i).h4 := by
  rfl

@[simp] theorem fallbackState_executionEnv (s : State) (input : ByteArray)
    (i : Nat) : (fallbackState s input i).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem fallbackState_halt (s : State) (input : ByteArray)
    (i : Nat) : (fallbackState s input i).halt = s.halt := by
  rfl

@[simp] theorem fallbackState_callStack (s : State) (input : ByteArray)
    (i : Nat) : (fallbackState s input i).callStack = s.callStack := by
  rfl

theorem fallbackState_wordAbove (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x200 ≤ address) :
    StackRunBridge.wordAt (fallbackState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt fallbackState
  exact PackedCombineMemory.writeHash_read_above s.memory
    (fallbackOutput s input i).h0 (fallbackOutput s input i).h1
    (fallbackOutput s input i).h2 (fallbackOutput s input i).h3
    (fallbackOutput s input i).h4 address haddress

theorem fallbackState_hashResult (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    StackRunBridge.hashAt32 (fallbackState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  have hdecoded : PackedHashInjectivity.decode (StackRunBridge.hashAt32 s) = h := by
    have hsame := congrArg PackedHashInjectivity.decode ctx.hash
    simpa only [PackedHashInjectivity.decode_embed] using hsame
  rw [show StackRunBridge.hashAt32 (fallbackState s input i) =
      StackMemory.hashAt (fallbackState s input i).memory by rfl,
    fallbackState_memory]
  rw [PackedCombineMemory.hashAt_writeHash]
  change fallbackOutput s input i = _
  simp only [fallbackOutput, hdecoded]

theorem endpointSpec_exists (provider : EndpointProvider)
    (s : State) (input : ByteArray) (i : Nat) :
    ∃ t, EndpointSpec s input i t := by
  classical
  by_cases hvalid : ∃ h, ValidMachineContext s input i h
  · obtain ⟨h, hctx⟩ := hvalid
    obtain ⟨t, ht⟩ := provider s input i h hctx
    refine ⟨t, {
      executionEnv := ht.executionEnv
      halt := ht.halt
      callStack := ht.callStack
      wordAbove := ht.wordAbove
      hashResult := ?_
      gasSteps := ?_ }⟩
    · intro supplied _hfit _hi ctx hmodel
      exact validEndpoint_hashResult_all hctx ht ctx hmodel
    · intro _supplied _hfit _hi _ctx _hcode _hfork _hrun _hnp
      exact ht.gasSteps
  · let t := fallbackState s input i
    refine ⟨t, {
      executionEnv := by simp [t]
      halt := by simp [t]
      callStack := by simp [t]
      wordAbove := ?_
      hashResult := ?_
      gasSteps := ?_ }⟩
    · intro address haddress
      exact fallbackState_wordAbove s input i address haddress
    · intro h _hfit _hi ctx _hmodel
      exact fallbackState_hashResult s input i h ctx
    · intro h hfit hi ctx hcode hfork hrun hnp
      exact False.elim (hvalid ⟨h, {
        fits := hfit
        blockIndex := hi
        blockContext := ctx
        code := hcode
        fork := hfork
        running := hrun
        noPrecompile := hnp }⟩)

noncomputable def nextStateFromWitness (provider : EndpointProvider)
    (s : State) (input : ByteArray) (i : Nat) : State :=
  Classical.choose (endpointSpec_exists provider s input i)

theorem nextStateFromWitness_spec (provider : EndpointProvider)
    (s : State) (input : ByteArray) (i : Nat) :
    EndpointSpec s input i (nextStateFromWitness provider s input i) :=
  Classical.choose_spec (endpointSpec_exists provider s input i)

/-- Package a conditional packed trace theorem as the total block kernel
expected by the existing outer compression loop. -/
noncomputable def kernelFromWitness
    (provider : EndpointProvider) : StackRunBridge.BlockKernel where
  nextState := nextStateFromWitness provider
  executionEnv := fun s input i =>
    (nextStateFromWitness_spec provider s input i).executionEnv
  halt := fun s input i =>
    (nextStateFromWitness_spec provider s input i).halt
  callStack := fun s input i =>
    (nextStateFromWitness_spec provider s input i).callStack
  wordAbove := fun s input i address haddress =>
    (nextStateFromWitness_spec provider s input i).wordAbove address haddress
  hashResult := fun s input i h hfit hi ctx hmodel =>
    (nextStateFromWitness_spec provider s input i).hashResult
      h hfit hi ctx hmodel
  gasSteps := fun s input i h hfit hi ctx hcode hfork hrun hnp =>
    Classical.choice ((nextStateFromWitness_spec provider s input i).gasSteps
      h hfit hi ctx hcode hfork hrun hnp)

#print axioms validEndpoint_hashResult_all
#print axioms fallbackState_wordAbove
#print axioms fallbackState_hashResult
#print axioms endpointSpec_exists
#print axioms nextStateFromWitness_spec
#print axioms kernelFromWitness

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedKernelChoice

import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCombineSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedDriverBody
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedKernelChoice

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Concrete packed endpoint provider

This module joins the empty-input shortcut and the actual packed compression
body with its five-store combine tail.  Its only public value is the endpoint
provider consumed by `PackedKernelChoice.kernelFromWitness`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEndpointProvider

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

private def blockValues (input : ByteArray) (i k : Nat) : UInt32 :=
  (CompressionCorrect.schedule (Padding.paddedMessage input)
    (DriverTrace.blockOffset i))[k]!

private theorem blockValues_eq_readLE32 (input : ByteArray) (i k : Nat)
    (hk : k < 16) :
    blockValues input i k =
      Crypto.Ripemd160.readLE32 (Padding.paddedMessage input)
        (DriverTrace.blockOffset i + k * 4) := by
  interval_cases k <;>
    simp [blockValues, CompressionCorrect.schedule, List.range']

private theorem hashAt32_eq_hashAt (s : State) :
    StackRunBridge.hashAt32 s = StackMemory.hashAt s.memory := by
  rfl

private theorem embedHashArray_hashArray (h : Compression.HashState) :
    StackRunBridge.embedHashArray (CompressionCorrect.hashArray h) =
      Compression.embedHash h := by
  rfl

private theorem input_eq_empty (input : ByteArray) (hempty : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using hempty
  · intro j hj
    simp [hempty] at hj

private theorem incoming_hash
    (s : State) (input : ByteArray) (i : Nat) (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h) :
    StackMemory.hashAt s.memory = Compression.embedHash h := by
  rw [← hashAt32_eq_hashAt]
  exact ctx.hash

private theorem bodyMemory_read_above (s middle : State)
    (input : ByteArray) (i address : Nat)
    (hmemory : middle.memory = PackedDriverBody.bodyMemory s input i)
    (haddress : 352 ≤ address) :
    MachineState.readWord middle.memory address =
      MachineState.readWord s.memory address := by
  rw [hmemory]
  unfold PackedDriverBody.bodyMemory
  exact PackedPreprocessTrace.preprocessReturned_read_above s
    (PackedDriverBounds.source i)
    [UInt256.ofNat 466, DriverTrace.blockOffsetWord i,
      Padding.paddedWord input] address haddress

private theorem bodyMemory_hash (s middle : State) (input : ByteArray)
    (i : Nat) (h : Compression.HashState)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmemory : middle.memory = PackedDriverBody.bodyMemory s input i) :
    StackMemory.hashAt middle.memory = Compression.embedHash h := by
  have h352 := bodyMemory_read_above s middle input i 352 hmemory (by omega)
  have h384 := bodyMemory_read_above s middle input i 384 hmemory (by omega)
  have h416 := bodyMemory_read_above s middle input i 416 hmemory (by omega)
  have h448 := bodyMemory_read_above s middle input i 448 hmemory (by omega)
  have h480 := bodyMemory_read_above s middle input i 480 hmemory (by omega)
  have hin := incoming_hash s input i h ctx
  unfold StackMemory.hashAt at hin ⊢
  rw [h352, h384, h416, h448, h480]
  exact hin

private theorem driver_endpoint_result (s : State) (input : ByteArray)
    (i : Nat) (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h) :
    PackedCombine.packedCombine (Compression.embedHash h)
        (PackedDriverBody.endpoint s input i h).regs =
      Compression.embedHash
        (CompressionCorrect.compressModel (blockValues input i) h) := by
  apply PackedCompressionBodyTrace.endpoint_result s
    (PackedDriverBounds.source i) h (UInt256.ofNat 466)
    (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) []
    (blockValues input i) (PackedDriverBounds.source_ge_512 i)
    (PackedDriverBounds.source_window_lt input hfit i hi)
  intro k hk
  have hblock : ScheduleCorrect.MessageBlockAt s.memory
      (PackedScheduleMemory.naturalp (PackedDriverBounds.source i))
      (Padding.paddedMessage input) (DriverTrace.blockOffset i) := by
    simpa [PackedScheduleMemory.naturalp, PackedDriverBounds.source,
      DriverTrace.messageOffsetWord] using ctx.messageBlock
  rw [blockValues_eq_readLE32 input i k hk]
  exact PackedDriverBounds.expectedWord_toNat s.memory
    (Padding.paddedMessage input)
    (PackedScheduleMemory.naturalp (PackedDriverBounds.source i))
    (DriverTrace.blockOffset i) k hk hblock

private theorem combineResult_wordAbove (s middle : State)
    (input : ByteArray) (i address : Nat) (h : Compression.HashState)
    (hmemory : middle.memory = PackedDriverBody.bodyMemory s input i)
    (haddress : 0x200 ≤ address) :
    StackRunBridge.wordAt
        (PackedCombineTrace.resultState middle
          (PackedDriverBody.endpoint s input i h).regs (UInt256.ofNat 466)
          (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) []) address =
      StackRunBridge.wordAt s address := by
  unfold StackRunBridge.wordAt PackedCombineTrace.resultState
  calc
    MachineState.readWord
        (PackedCombineTrace.outputMemory middle
          (PackedDriverBody.endpoint s input i h).regs) address =
      MachineState.readWord middle.memory address := by
        unfold PackedCombineTrace.outputMemory
        exact PackedCombineMemory.writeHash_read_above middle.memory
          (PackedCombineTrace.outputHash middle
            (PackedDriverBody.endpoint s input i h).regs).h0
          (PackedCombineTrace.outputHash middle
            (PackedDriverBody.endpoint s input i h).regs).h1
          (PackedCombineTrace.outputHash middle
            (PackedDriverBody.endpoint s input i h).regs).h2
          (PackedCombineTrace.outputHash middle
            (PackedDriverBody.endpoint s input i h).regs).h3
          (PackedCombineTrace.outputHash middle
            (PackedDriverBody.endpoint s input i h).regs).h4
          address haddress
    _ = MachineState.readWord s.memory address :=
      bodyMemory_read_above s middle input i address hmemory (by omega)

private theorem combineResult_hash (s middle : State) (input : ByteArray)
    (i : Nat) (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmemory : middle.memory = PackedDriverBody.bodyMemory s input i) :
    StackRunBridge.hashAt32
        (PackedCombineTrace.resultState middle
          (PackedDriverBody.endpoint s input i h).regs (UInt256.ofNat 466)
          (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) []) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  have hmiddle := bodyMemory_hash s middle input i h ctx hmemory
  have hcombine := driver_endpoint_result s input i h hfit hi ctx
  change StackMemory.hashAt
      (PackedCombineTrace.outputMemory middle
        (PackedDriverBody.endpoint s input i h).regs) = _
  calc
    StackMemory.hashAt
        (PackedCombineTrace.outputMemory middle
          (PackedDriverBody.endpoint s input i h).regs) =
      PackedCombineTrace.outputHash middle
        (PackedDriverBody.endpoint s input i h).regs := by
        unfold PackedCombineTrace.outputMemory
        rw [PackedCombineMemory.hashAt_writeHash]
    _ = Compression.embedHash
        (CompressionCorrect.compressModel (blockValues input i) h) := by
      unfold PackedCombineTrace.outputHash
      rw [hmiddle]
      exact hcombine
    _ = StackRunBridge.embedHashArray
        (CompressionCorrect.hashArray
          (CompressionCorrect.compressModel (blockValues input i) h)) := by
      rw [embedHashArray_hashArray]
    _ = StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
      apply congrArg StackRunBridge.embedHashArray
      exact CompressionCorrect.compressModel_eq_compressBlock
        (Padding.paddedMessage input) (DriverTrace.blockOffset i) h

private theorem nonempty_endpoint (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : PackedKernelChoice.ValidMachineContext s input i h)
    (hempty : input.size ≠ 0) :
    ∃ t, PackedKernelChoice.ValidEndpoint s input i h t := by
  have gdispatch := FastEmptyBlock.gasSteps_nonempty s input i ctx.fits
    (Nat.pos_of_ne_zero hempty) ctx.blockContext.calldata ctx.code ctx.fork
    ctx.running ctx.noPrecompile
  have hhash := incoming_hash s input i h ctx.blockContext
  obtain ⟨middle, bodyTrace, hstack, hmemory, henv, hhalt, hcalls,
      hpc, hactive⟩ := PackedDriverBody.gasSteps_driverBody s input i h
        ctx.fits ctx.blockIndex hhash ctx.code ctx.fork ctx.running
        ctx.noPrecompile
  let ep := PackedDriverBody.endpoint s input i h
  let t := PackedCombineTrace.resultState middle ep.regs (UInt256.ofNat 466)
    (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) []
  have hmiddleCode : middle.executionEnv.code = submissionBytecode := by
    rw [henv]
    exact ctx.code
  have hmiddleFork : middle.fork = .Osaka := by
    change middle.executionEnv.fork = .Osaka
    rw [henv]
    exact ctx.fork
  have hmiddleNp : Precompile.isPrecompileWithConfig
      middle.executionEnv.precompileConfig middle.executionEnv.fork
      middle.executionEnv.codeAddr = false := by
    rw [henv]
    exact ctx.noPrecompile
  have tailRaw := PackedCombineSite.gasSteps_combineTail_return466 middle
    ep.regs (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) []
    hactive (by decide) hmiddleCode hmiddleFork hhalt hmiddleNp
  have htailStack : PackedCombineTrace.entryStack ep.regs
      (UInt256.ofNat 466) (DriverTrace.blockOffsetWord i)
      (Padding.paddedWord input) [] = middle.stack := by
    rw [show ep = PackedDriverBody.endpoint s input i h by rfl]
    unfold PackedDriverBody.endpoint PackedCompressionBodyTrace.endpoint
    rw [PackedCombineSite.entryStack_endpoint]
    simpa only [PackedDriverBody.endpoint, PackedCompressionBodyTrace.endpoint,
      List.append_nil] using hstack.symm
  have htailStart : PackedCombineTrace.entryState middle ep.regs
      (UInt256.ofNat 466) (DriverTrace.blockOffsetWord i)
      (Padding.paddedWord input) [] = middle := by
    unfold PackedCombineTrace.entryState
    rw [hpc.symm, htailStack]
  have tailTrace : GasSteps middle t := by
    exact GasSteps.cast tailRaw htailStart rfl
  have fullTrace : GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned t input i) := by
    exact GasSteps.cast (gdispatch.trans (bodyTrace.trans tailTrace))
      (by rfl) (by rfl)
  refine ⟨t, {
    executionEnv := ?_
    halt := ?_
    callStack := ?_
    wordAbove := ?_
    hashResult := ?_
    gasSteps := ⟨fullTrace⟩ }⟩
  · exact henv
  · exact hhalt.trans ctx.running.symm
  · exact hcalls
  · intro address haddress
    exact combineResult_wordAbove s middle input i address h hmemory haddress
  · intro _hmodel
    exact combineResult_hash s middle input i h ctx.fits ctx.blockIndex
      ctx.blockContext hmemory

private theorem empty_endpoint (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState)
    (ctx : PackedKernelChoice.ValidMachineContext s input i h)
    (hempty : input.size = 0) :
    ∃ t, PackedKernelChoice.ValidEndpoint s input i h t := by
  let t := FastEmptyBlock.resultState s input i
  have gempty := FastEmptyBlock.gasSteps_empty s input i hempty
    ctx.blockContext.calldata ctx.code ctx.fork ctx.running ctx.noPrecompile
  have fullTrace : GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned t input i) := by
    exact GasSteps.cast gempty (by rfl) (by
      simp [t, DriverTrace.compressReturned, FastEmptyBlock.resultState])
  refine ⟨t, {
    executionEnv := by simp [t]
    halt := by simp [t]
    callStack := by simp [t]
    wordAbove := ?_
    hashResult := ?_
    gasSteps := ⟨fullTrace⟩ }⟩
  · intro address haddress
    unfold StackRunBridge.wordAt
    exact FastEmptyBlock.resultState_word_above s input i address haddress
  · intro hmodel
    have hinput := input_eq_empty input hempty
    subst input
    have hi := ctx.blockIndex
    have hi0 : i = 0 := by
      simp [DriverTrace.blockCount, Padding.paddedLength] at hi
      omega
    subst i
    change StackMemory.hashAt
      (FastEmptyBlock.resultState s ByteArray.empty 0).memory = _
    rw [FastEmptyBlock.resultState_hashAt, hmodel]
    change FastEmptyBlock.emptyHash =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock Crypto.Ripemd160.H0
          (Padding.paddedMessage ByteArray.empty) 0)
    rw [FastEmptyBlock.compress_empty]
    rfl

/-- The concrete provider used to instantiate the total packed block kernel. -/
def endpointProvider : PackedKernelChoice.EndpointProvider := by
  intro s input i h ctx
  by_cases hempty : input.size = 0
  · exact empty_endpoint s input i h ctx hempty
  · exact nonempty_endpoint s input i h ctx hempty

#print axioms endpointProvider

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEndpointProvider

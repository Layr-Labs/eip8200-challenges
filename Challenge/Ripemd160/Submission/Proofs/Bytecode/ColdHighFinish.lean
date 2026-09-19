import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighFinish
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerIteration ColdHighTrace StaggerPersistentFrame

def resultHash (input : ByteArray) (i : Nat) : Compression.HashState :=
  PersistentStaggerFunctional.result (tableState input i).memory (hashes input i)

def resultState (input : ByteArray) (i : Nat) : State :=
  StaggerPersistentSerialize.result (tableState input i) (resultHash input i)
    (Padding.paddedWord input) (Padding.paddedWord input) maskRho

theorem last_index (input : ByteArray) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    i + 1 = DriverTrace.blockCount input := by
  simp only [DriverTrace.blockCount, Padding.paddedLength, hh, DriverTrace.blockOffset]
  omega

private theorem aligned (input : ByteArray) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) : input.size % 64 = 0 := by
  simp [hh, DriverTrace.blockOffset]

private theorem next_eq (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    StaggerPersistentLoopRaw.nextOffset (DriverTrace.blockOffsetWord i) =
      Padding.paddedWord input := by
  have hsum : input.size + 64 < 2^256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [PaddingTraceGeneral.paddedWord_aligned input hfit (aligned input i hh)]
  change UInt256.ofNat (DriverTrace.blockOffset i) + UInt256.ofNat 64 = _
  rw [← hh, Word.ofNat_add_ofNat hsum]

private theorem next_nat (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    (StaggerPersistentLoopRaw.nextOffset (DriverTrace.blockOffsetWord i)).toNat =
      input.size + 64 := by
  have hsum : input.size + 64 < 2^256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [next_eq input hfit i hh,
    PaddingTraceGeneral.paddedWord_aligned input hfit (aligned input i hh),
    Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsum]

private opaque compose3 {s t u v : State}
    (a : GasSteps s t) (b : GasSteps t u) (c : GasSteps u v) : GasSteps s v :=
  a.trans (b.trans c)

/-- Compression and final serialization at an arbitrary backing state. -/
private opaque finish (s : State) (e : Shared32Sites.Env s)
    (h : Compression.HashState) (off limit : UInt256)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hnext : StaggerPersistentLoopRaw.nextOffset off = limit)
    (hfit : s.executionEnv.calldata.size < 2^256)
    (hdispatch : s.executionEnv.calldata.size ≠
      (StaggerPersistentLoopRaw.nextOffset off).toNat) :
    GasSteps
      {s with pc := UInt256.ofNat 859, stack := frame h off limit maskRho}
      (StaggerPersistentSerialize.result s
        (PersistentStaggerFunctional.result s.memory h) limit limit maskRho) := by
  have gb := Shared32Core.gasSteps_body s e h off limit maskRho (by decide) hactive
  have ge := StaggerPersistentLoopSites.gasSteps_exit s
    (PersistentStaggerFunctional.result s.memory h) off limit maskRho (by decide)
    e.run (by rw [hnext]) hfit hdispatch e.code e.fork e.np
  have go := StaggerPersistentSerialize.gasSteps s limit limit
    (PersistentStaggerFunctional.result s.memory h) [] (by decide)
    e.run e.code e.fork e.np
  have hend :
      ({s with
        pc := UInt256.ofNat 4644
        stack := frame (PersistentStaggerFunctional.result s.memory h)
          (StaggerPersistentLoopRaw.nextOffset off) limit maskRho} : State) =
      {s with
        pc := UInt256.ofNat 4644
        stack := frame (PersistentStaggerFunctional.result s.memory h) limit limit maskRho} := by
    rw [hnext]
  exact compose3 gb (ge.cast rfl hend) go

opaque gasSteps (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) :
    GasSteps
      {tableState input i with
        pc := UInt256.ofNat 859
        stack := frame (hashes input i) (DriverTrace.blockOffsetWord i)
          (Padding.paddedWord input) maskRho}
      (resultState input i) := by
  have he : Shared32Sites.Env (tableState input i) :=
    ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i⟩
  have hcal : (tableState input i).executionEnv.calldata = input := states_calldata input i
  exact finish (tableState input i) he (hashes input i)
    (DriverTrace.blockOffsetWord i) (Padding.paddedWord input)
    (by have ha := tableState_active input hfit i hi; omega)
    (next_eq input hfit i hh)
    (by rw [hcal]; unfold CalldataFits at hfit; norm_num at hfit ⊢; omega)
    (by rw [hcal, next_nat input hfit i hh]; omega)

theorem resultHash_spec (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) :
    CompressionCorrect.hashArray (resultHash input i) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input) := by
  have hr := ColdHighReady.ready input hfit hpositive i hi hh
  have hf := PersistentStaggerFunctional.result_compressBlock
    (tableState input i).memory (Padding.paddedMessage input)
    (DriverTrace.blockOffset i) (hashes input i) hr
  rw [hashArray_hashes input hfit hpositive i (by omega)] at hf
  rw [← last_index input i hh, StackRunBridge.hashAfter_succ]
  exact hf

theorem returned_spec (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (i : Nat) (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) :
    (resultState input i).hReturn = spec input :=
  StaggerPersistentSerialize.returned_spec_of_hashArray (tableState input i) input
    (Padding.paddedWord input) (Padding.paddedWord input) maskRho (resultHash input i)
    (resultHash_spec input hfit hpositive i hi hh)

@[simp] theorem resultState_halt (input : ByteArray) (i : Nat) :
    (resultState input i).halt = .Returned := rfl

@[simp] theorem resultState_callStack (input : ByteArray) (i : Nat) :
    (resultState input i).callStack = [] := states_callStack input i

#print axioms gasSteps
#print axioms returned_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighFinish

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
    (StaggerPersistentLoopRaw.nextOffset (DriverTrace.messageOffsetWord i))
    (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size)) maskRho

theorem last_index (input : ByteArray) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    i + 1 = DriverTrace.blockCount input := by
  simp only [DriverTrace.blockCount, Padding.paddedLength, hh, DriverTrace.blockOffset]
  omega

private theorem aligned (input : ByteArray) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) : input.size % 64 = 0 := by
  simp [hh, DriverTrace.blockOffset]

private theorem next_nat (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    (StaggerPersistentLoopRaw.nextOffset (DriverTrace.messageOffsetWord i)).toNat =
      1120 + input.size := by
  have hsum : 1120 + input.size < 2^256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  change (UInt256.ofNat (Padding.messageOffset + DriverTrace.blockOffset i) + UInt256.ofNat 64).toNat = _
  rw [Word.ofNat_add_ofNat (by unfold Padding.messageOffset; omega), Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by unfold Padding.messageOffset; omega)]
  unfold Padding.messageOffset
  omega

private theorem limit_nat (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hh : input.size = DriverTrace.blockOffset i) :
    (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size)).toNat = 1087 + input.size := by
  have hsum : 1087 + input.size < 2^256 := by
    unfold CalldataFits at hfit
    norm_num at hfit ⊢
    omega
  rw [PadLimitArithmetic.coldRounded_input input hfit, Word.word_toNat_ofNat]
  have hz := aligned input i hh
  have hp : Padding.paddedLength input.size = input.size + 64 := by
    unfold Padding.paddedLength; omega
  rw [hp, Nat.mod_eq_of_lt (by omega)]
  omega

private opaque compose3 {s t u v : State}
    (a : GasSteps s t) (b : GasSteps t u) (c : GasSteps u v) : GasSteps s v :=
  a.trans (b.trans c)

/-- Compression and final serialization at an arbitrary backing state. -/
private opaque finish (s : State) (e : Shared32Sites.Env s)
    (h : Compression.HashState) (off limit : UInt256)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hbound : limit.toNat ≤ (StaggerPersistentLoopRaw.nextOffset off).toNat)
    (hmiss : StaggerPersistentLoopRaw.nextOffset off ≠ limit) :
    GasSteps
      {s with pc := UInt256.ofNat 808, stack := frame h off limit maskRho}
      (StaggerPersistentSerialize.result s
        (PersistentStaggerFunctional.result s.memory h)
        (StaggerPersistentLoopRaw.nextOffset off) limit maskRho) := by
  have gb := Shared32Core.gasSteps_body s e h off limit maskRho (by decide) hactive
  have ge := StaggerPersistentLoopSites.gasSteps_exit s
    (PersistentStaggerFunctional.result s.memory h) off limit maskRho (by decide)
    e.run hbound hmiss e.code e.fork e.np
  have go := StaggerPersistentSerialize.gasSteps s (StaggerPersistentLoopRaw.nextOffset off) limit
    (PersistentStaggerFunctional.result s.memory h) [] (by decide)
    e.run e.code e.fork e.np
  exact compose3 gb ge go

opaque gasSteps (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i < DriverTrace.blockCount input)
    (hh : input.size = DriverTrace.blockOffset i) :
    GasSteps
      {tableState input i with
        pc := UInt256.ofNat 808
        stack := frame (hashes input i) (DriverTrace.messageOffsetWord i)
          (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size)) maskRho}
      (resultState input i) := by
  have he : Shared32Sites.Env (tableState input i) :=
    ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i⟩
  exact finish (tableState input i) he (hashes input i)
    (DriverTrace.messageOffsetWord i) (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size))
    (by have ha := tableState_active input hfit i hi; omega)
    (by rw [next_nat input hfit i hh, limit_nat input hfit i hh]; omega)
    (by
      intro heq
      have ht := congrArg UInt256.toNat heq
      rw [next_nat input hfit i hh, limit_nat input hfit i hh] at ht
      omega)

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
    (StaggerPersistentLoopRaw.nextOffset (DriverTrace.messageOffsetWord i))
    (PadLimitArithmetic.coldRounded (UInt256.ofNat input.size)) maskRho (resultHash input i)
    (resultHash_spec input hfit hpositive i hi hh)

@[simp] theorem resultState_halt (input : ByteArray) (i : Nat) :
    (resultState input i).halt = .Returned := rfl

@[simp] theorem resultState_callStack (input : ByteArray) (i : Nat) :
    (resultState input i).callStack = [] := states_callStack input i

#print axioms gasSteps
#print axioms returned_spec
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighFinish

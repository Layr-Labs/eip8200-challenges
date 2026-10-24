import Challenge.Modexp.Submission.Proofs.Cycle.ProductStep
import Challenge.Modexp.Submission.Proofs.Cycle.Return
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.Finish
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open CycleSubmission.ControlArithmetic (value)

structure Outcome (start : State) (expected : ByteArray) where
  state : State
  trace : GasSteps start state
  halt : state.halt = .Returned
  bytes : state.hReturn = expected
  calls : state.callStack = start.callStack

theorem Outcome.eventually {start : State} {expected : ByteArray}
    (out : Outcome start expected) (hstack : start.callStack = []) :
    ∃ gas0, ∀ gas, gas0 ≤ gas → Eval (withGas start gas) (.returned expected) := by
  refine ⟨out.trace.cost, ?_⟩
  intro gas hgas
  apply Eval.iff_steps_halted.mpr
  refine ⟨withGas out.state (gas-out.trace.cost), out.trace.trace gas hgas, ?_, ?_, ?_⟩
  · change out.state.halt ≠ .Running
    rw [out.halt]
    intro h; cases h
  · change out.state.callStack = []
    exact out.calls.trans hstack
  · change out.state.toResult = .returned expected
    rw [State.toResult_returned out.state out.halt, out.bytes]

structure Packed (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256) (rest : List UInt256) where
  state : State
  trace : GasSteps {s with pc := UInt256.ofNat 10867, stack := NormalizeMeaning.frame a n slot0 slot1 rest} state
  pc : state.pc = UInt256.ofNat 11000
  frame : state.stack = NormalizeMeaning.frame a n slot0 slot1 rest
  env : state.executionEnv = s.executionEnv
  halt : state.halt = s.halt
  active : state.activeWords = s.activeWords
  represented : Challenge.Modexp.Submission.Proofs.Fast.Model.FastRepresents state.memory 2112 8 (value a)
  calls : state.callStack = s.callStack

noncomputable def pack (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : NormalizeMeaning.MemoryInput s.memory a n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix) (hv : value a < 2^2048) :
    Packed s a n slot0 slot1 rest :=
  ⟨PackExecution.result s a n slot0 slot1 rest,
    PackExecution.gasSteps s a n slot0 slot1 rest env hm hcap hact,
    rfl, rfl, rfl, rfl, rfl, PackExecution.represents s a n slot0 slot1 rest ha hv, rfl⟩

noncomputable def serialize (s : State) (a n : Nat → UInt256) (slot0 slot1 : UInt256)
    (rest : List UInt256) (env : Environment Artifact.artifact .Osaka s)
    (hm : NormalizeMeaning.MemoryInput s.memory a n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix) (hv : value a < 2^2048) :
    Outcome {s with pc := UInt256.ofNat 10867, stack := NormalizeMeaning.frame a n slot0 slot1 rest}
      (Precompile.natToBytes (value a) 256) := by
  obtain ⟨packed, hp, pc, frame, en, halt, active, rep, calls⟩ := pack s a n slot0 slot1 rest env hm hcap hact ha hv
  have cap : (NormalizeMeaning.frame a n slot0 slot1 rest).length ≤ 1021 := by
    simp only [NormalizeMeaning.frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have act : 88 ≤ packed.activeWords.toNat := by rw [active]; exact hact
  have hr := Return.gasSteps packed (NormalizeMeaning.frame a n slot0 slot1 rest)
    (env.transfer en halt) cap act
  have he : {packed with pc := UInt256.ofNat 11000, stack := NormalizeMeaning.frame a n slot0 slot1 rest} = packed :=
    SquareExecution.reset_self _ _ _ pc frame
  rw [he] at hr
  refine ⟨Return.result packed (NormalizeMeaning.frame a n slot0 slot1 rest), hp.trans hr, rfl, ?_, calls⟩
  exact Return.returned_bytes packed (NormalizeMeaning.frame a n slot0 slot1 rest) (value a) rep

structure Computed (s : State) (inv : UInt256) (a b n : Nat → UInt256)
    (rest : List UInt256) (N x : Nat) where
  state : State
  out : Nat → UInt256
  slot0 : UInt256
  slot1 : UInt256
  trace : GasSteps {s with pc := UInt256.ofNat 8202, stack := ProductMeaning.frame0 inv a b n rest} state
  memory : NormalizeMeaning.MemoryInput state.memory out n
  frame : state.stack = NormalizeMeaning.frame out n slot0 slot1 rest
  pc : state.pc = UInt256.ofNat 10867
  env : state.executionEnv = s.executionEnv
  halt : state.halt = s.halt
  active : state.activeWords = s.activeWords
  calls : state.callStack = s.callStack
  bound : ∀ i < 9, (out i).toNat < radix
  valueEq : value out = value b*x%N

noncomputable def compute (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : ProductMeaning.Memory0 s.memory inv a b n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix) (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N x : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNsize : N < 2^2048) (hodd : Odd N)
    (hB : value b < N) (hform : value a ≡ x*radix^9 [MOD N]) : Computed s inv a b n rest N x := by
  have hNR : N < radix^9 := Nat.lt_trans hNsize (by norm_num [radix])
  have arith := ProductStep.arithmetic inv a b n ha hb hn N x hn0 hNvalue hinv hN hNR hodd hB hform
  exact ⟨ProductStep.result s inv a b n rest, ProductStep.digits inv a b n,
    ProductStep.slot0 inv a b n, productQ7 inv a b n,
    ProductStep.gasSteps s inv a b n rest env hm hcap hact ha hb hn N hn0 hinv,
    ProductStep.memory_output s inv a b n rest hm, ProductStep.frame_output s inv a b n rest,
    ProductStep.pc_output s inv a b n rest, ProductStep.executionEnv_eq s inv a b n rest,
    ProductStep.halt_eq s inv a b n rest, ProductStep.active_eq s inv a b n rest,
    ProductStep.calls_eq s inv a b n rest, arith.1, arith.2⟩

noncomputable def product (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hm : ProductMeaning.Memory0 s.memory inv a b n)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
    (ha : ∀ i < 9, (a i).toNat < radix) (hb : ∀ i < 9, (b i).toNat < radix)
    (hn : ∀ i < 9, (n i).toNat < radix)
    (N x : Nat) (hn0 : (n 0).toNat = N % radix) (hNvalue : value n = N)
    (hinv : (N*inv.toNat+1) % 2^256 = 0)
    (hN : 0 < N) (hNsize : N < 2^2048) (hodd : Odd N)
    (hB : value b < N) (hform : value a ≡ x*radix^9 [MOD N]) :
    Outcome {s with pc := UInt256.ofNat 8202, stack := ProductMeaning.frame0 inv a b n rest}
      (Precompile.natToBytes (value b*x % N) 256) := by
  obtain ⟨st, out, slot0, slot1, ht, mem, frame, pc, en, halt, active, calls, bound, valueEq⟩ :=
    compute s inv a b n rest env hm hcap hact ha hb hn N x hn0 hNvalue hinv hN hNsize hodd hB hform
  have act : 88 ≤ st.activeWords.toNat := by rw [active]; exact hact
  have hv : value out < 2^2048 := by
    rw [valueEq]; exact Nat.lt_trans (Nat.mod_lt _ hN) hNsize
  obtain ⟨done, tr, returned, bytes, callsDone⟩ := serialize st out n slot0 slot1 rest
    (env.transfer en halt) mem hcap act bound hv
  have he : {st with pc := UInt256.ofNat 10867, stack := NormalizeMeaning.frame out n slot0 slot1 rest} = st :=
    SquareExecution.reset_self _ _ _ pc frame
  rw [he] at tr
  refine ⟨done, ht.trans tr, returned, ?_, callsDone.trans calls⟩
  rw [valueEq] at bytes
  exact bytes

end CycleSubmission.Finish

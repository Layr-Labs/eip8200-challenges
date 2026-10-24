import Challenge.Modexp.Submission.Proofs.Cycle.EntryBinding
import Challenge.Modexp.Submission.Proofs.Cycle.SquareLoop
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
set_option exponentiation.threshold 4096
namespace CycleSubmission.EntryContract
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Model
open CycleSubmission.EntryMeaning CycleSubmission.InputWords CycleSubmission.WordArithmetic
open CycleSubmission.ControlArithmetic (value)
open HistoricalSearch.CRTMemoryCells

theorem keeps_base (s : State) (f : Caller) (start count : Nat)
    (hs : 256 ≤ start) (he : start+count ≤ 768) :
    MachineState.readPadded (EntryBinding.entered s f).memory start count =
      MachineState.readPadded s.memory start count := by
  apply readPadded_storeCells
  intro c hc
  simp only [cells, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp <;> omega

theorem counter (s : State) (f : Caller) :
    CounterControl.counter (EntryBinding.entered s f) = f.counter := by
  simp (disch := decide) only [CounterControl.counter, EntryBinding.entered, result, cells,
    storeCells, writeCell, NormalizeMeaning.readStore, Challenge.EvmProof.Memory.readWord_writeWord]

structure Outcome (s : State) (f : Caller) (k N B x : Nat) where
  state : State
  inv : UInt256
  a : Nat → UInt256
  n : Nat → UInt256
  trace : GasSteps {s with pc := UInt256.ofNat 5964, stack := saved f} state
  frame : state.stack = SquareMeaning.frame0 inv a SquareStep.zeroWords n (saved f)
  pc : state.pc = UInt256.ofNat 6153
  memory : SquareMeaning.Memory0 state.memory inv a SquareStep.zeroWords n
  env : state.executionEnv = s.executionEnv
  halt : state.halt = s.halt
  active : state.activeWords = s.activeWords
  counter : CounterControl.counter state = UInt256.ofNat (k-1)
  aBound : ∀ i < 9, (a i).toNat < radix
  nBound : ∀ i < 9, (n i).toNat < radix
  n0 : (n 0).toNat = N % radix
  nValue : value n = N
  inverse : (N*inv.toNat+1) % 2^256 = 0
  base : FastRepresents state.memory 256 8 B
  form : value a ≡ x*radix^9 [MOD N]
  calls : state.callStack = s.callStack

noncomputable def prepare (s : State) (f : Caller) (k N A B x : Nat)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : f.tail.length ≤ 944) (hact : 88 ≤ s.activeWords.toNat)
    (hcounter : f.counter = UInt256.ofNat (k-1))
    (hn : FastRepresents s.memory 0 8 N) (ha : FastRepresents s.memory 2368 8 A)
    (hb : FastRepresents s.memory 256 8 B)
    (hinv : (N*(MachineState.readWord s.memory 2720).toNat+1) % 2^256 = 0)
    (hform : A ≡ x*2^2048 [MOD N]) : Outcome s f k N B x := by
  have hA := scaled_represents ha
  have hN := ordinary_represents hn
  refine ⟨EntryBinding.entered s f, MachineState.readWord s.memory 2720,
    scaled s.memory 2368, ordinary s.memory 0,
    EntryBinding.gasSteps s f env hcap hact, rfl, rfl, memory_output s f,
    rfl, rfl, rfl, ?_, hA.1, hN.1, ?_, hN.2, hinv, ?_, ?_, rfl⟩
  · rw [counter, hcounter]
  · have h := low_value hn 0 (by decide)
    simpa only [radix, ordinary, show (0:Nat)<8 by decide, if_true, Nat.mul_zero, Nat.pow_zero, Nat.div_one] using h
  · apply (fastRepresents_congr (a := (EntryBinding.entered s f).memory) (b := s.memory) ?_ B).mpr hb
    intro j hj
    unfold MachineState.readWord
    rw [keeps_base s f (256+32*j) 32 (by omega) (by omega)]
  · change value (scaled s.memory 2368) % N = (x*radix^9)%N
    change (HistoricalSearch.MixedMontgomery.weighted (2^240) 9 (fun i => (scaled s.memory 2368 i).toNat)) % N = _
    rw [hA.2]
    have h := hform.mul_right (2^112)
    have hr : (2:Nat)^2048*2^112 = radix^9 := by
      rw [radix, ← Nat.pow_add, ← Nat.pow_mul]
    calc
      A*2^112%N = ((x*2^2048)*2^112)%N := h
      _ = (x*radix^9)%N := by rw [Nat.mul_assoc, hr]

end CycleSubmission.EntryContract

import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduledTailRaw
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# A concrete kernel witness against the round-45 carry-through experiment

The attempted SWAP7 deletion carries the `.re`/`.le` transposition into the
terminal fold. Its changed SWAP at PC 4530 moves that permutation but does not
restore the ordered chaining words. This certificate is deliberately separate
from the installed artifact: neither the rejected template nor its input is
claimed to be the installed correct compressor.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Round45TailCounterexample
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace

/-- The rejected PC-4530 operand change: SWAP3 becomes SWAP6. -/
def rejectedChunk1 : List Instr := [
  .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .SHR, .op .ADD,
  .op (.Swap ⟨2, by decide⟩), .op .ADD,
  .op (.Swap ⟨5, by decide⟩),
  .push ⟨1, by decide⟩ (UInt256.ofNat 144), .op .SHR, .op .ADD,
  .op (.Dup ⟨15, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩) ]

def rejectedTemplate : List Instr := ScheduledTailRaw.chunk0 ++ rejectedChunk1 ++
  ScheduledTailRaw.chunk2 ++ ScheduledTailRaw.chunk3

def transposed (q : ScheduledTailRaw.Input) : ScheduledTailRaw.Input :=
  {q with re := q.le, le := q.re}

/-- Scalar witness; it is not asserted to be a reachable RIPEMD round state. -/
def witness : ScheduledTailRaw.Input :=
  { ld := 0, lb := 0, le := 1, la := 0, k := 0, lc := 0,
    re := 0, rc := 0, ra := 0, rd := 0, rb := 0,
    factor := 0, lower := UInt256.ofNat 0xffffffff,
    cache140 := 0, cache350 := 0, cache310 := 0, cache190 := 0,
    literal72 := 0, literal28 := 0,
    h4 := 0, h1 := 0, h2 := 0, h3 := 0, h0 := 0, off := 0, limit := 0 }

theorem rejected_same_byte_length :
    (rejectedTemplate.map Instr.size).sum = (ScheduledTailRaw.template.map Instr.size).sum := by
  decide

/-- The already-installed last 24 one-byte operations, starting at PC 4535.
This freezes the baseline for controlled terminal-fold searches; it does not
change or substitute for the installed artifact's execution theorem. -/
def installedSuffix : List Instr :=
  [.op (.Dup ⟨15, by decide⟩), .op .ADD, .op (.Dup ⟨8, by decide⟩)] ++
    ScheduledTailRaw.chunk2 ++ ScheduledTailRaw.chunk3

theorem installedSuffix_length : installedSuffix.length = 24 := by decide

theorem installedSuffix_byte_length : (installedSuffix.map Instr.size).sum = 24 := by decide

theorem installedSuffix_cost :
    (installedSuffix.map (Meter.instrStaticCost .Osaka)).sum = 71 := by decide

/-- Even exact byte span and unchanged arithmetic opcodes do not prove the
same terminal result after a carried lane permutation. -/
theorem rejected_fold_not_equal (s : State) (hrun : s.halt = .Running) :
    runInstrSeq rejectedTemplate
      {s with pc := UInt256.ofNat 4509, stack := ScheduledTailRaw.stack0 (transposed witness) []} ≠
    runInstrSeq ScheduledTailRaw.template
      {s with pc := UInt256.ofNat 4509, stack := ScheduledTailRaw.stack0 witness []} := by
  simp (config := { maxSteps := 600000 }) (discharger := omega)
    [rejectedTemplate, rejectedChunk1, ScheduledTailRaw.template,
     ScheduledTailRaw.chunk0, ScheduledTailRaw.chunk1,
     ScheduledTailRaw.chunk2, ScheduledTailRaw.chunk3,
     ScheduledTailRaw.stack0, transposed, witness,
     runInstrSeq, DataStepper.runInstr, UInt256.succ, Instr.size,
     hrun, List.getElem?_cons_zero, List.exchange,
     Word.word_toNat_ofNat, Word.literal_eq_ofNat]
  decide

#print axioms rejected_same_byte_length
#print axioms installedSuffix_cost
#print axioms rejected_fold_not_equal
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Round45TailCounterexample

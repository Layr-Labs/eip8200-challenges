import Challenge.Ripemd160.Submission.Proofs.Bytecode.RoundTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ScheduleActiveWords

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateNeutralLoads

open EvmSemantics
open EvmSemantics.EVM

/-- The helper overwrites its incoming PC and stack. Its output frame can be
chosen without changing the memory or the active-memory endpoint. -/
theorem roundReturned_reframe (s : State) (pc : UInt256)
    (stack : List UInt256) (base : UInt256) (j : Nat)
    (wordIndex rotation k oldReturn newReturn : UInt256)
    (oldRest newRest : List UInt256) :
    RoundTrace.roundReturned {s with pc := pc, stack := stack}
        base j wordIndex rotation k newReturn newRest =
      {RoundTrace.roundReturned s base j wordIndex rotation k oldReturn oldRest
        with pc := newReturn, stack := newRest} := by
  rfl

theorem tableAddress_toNat (base i : Nat) (hi : i < 80)
    (hlo : 31 ≤ base) (hbase : base + i < 2 ^ 256) :
    (TableTrace.tableAddress (UInt256.ofNat base) (UInt256.ofNat i)).toNat =
      base - 31 + i := by
  unfold TableTrace.tableAddress
  rw [Challenge.EvmProof.Word.ofNat_sub_ofNat hlo (by omega),
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- All packed table reads fit below the schedule's 67-word high-water. -/
theorem tableAtReturned_neutral (s : State) (base i : Nat)
    (hi : i < 80) (hlo : 31 ≤ base) (hbase : base + 80 ≤ 67 * 32)
    (hactive : 67 ≤ s.activeWords.toNat) (returnDest : UInt256)
    (rest : List UInt256) :
    TableTrace.tableAtReturned s (UInt256.ofNat base) (UInt256.ofNat i)
        returnDest rest =
      {s with
        pc := returnDest
        stack := TableTrace.tableValue s (UInt256.ofNat base)
          (UInt256.ofNat i) :: rest} := by
  have ha : s.activeWordsAfterUInt256
      (TableTrace.tableAddress (UInt256.ofNat base) (UInt256.ofNat i)).toNat 32 =
      s.activeWords := by
    apply ScheduleActiveWords.activeWordsAfterUInt256_eq
    rw [tableAddress_toNat base i hi hlo (by omega)]
    omega
  simp only [TableTrace.tableAtReturned, ha]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateNeutralLoads

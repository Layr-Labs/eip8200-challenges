import Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory
import Challenge.Modexp.Submission.Proofs.Fast.Model
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace CycleSubmission.CallerMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast StagedOperand

/- The memory contracts are extracted from the accepted v14 CRTLoopEntry and
SquareResult proofs, without importing their obsolete executable routes. -/
def memory (mem : ByteArray) : ByteArray := SquarePartialClear.memory (stage mem 2112 8)

theorem readWord (mem : ByteArray) (addr : Nat)
    (hd : addr + 32 ≤ 2048 ∨ 2624 ≤ addr) :
    MachineState.readWord (memory mem) addr = MachineState.readWord mem addr := by
  unfold memory
  rw [SquarePartialClear.readWord_outside _ addr (by omega),
    read_stage_outside mem 2112 8 addr (by omega)]

theorem represents_stage (mem : ByteArray) (a : Nat)
    (ha : Model.FastRepresents mem 2112 8 a) :
    Model.FastRepresents (stage mem 2112 8) 2368 8 a := by
  unfold Model.FastRepresents Model.fastLimbs at *
  have heq : (List.range 8).map (fun k =>
      (MachineState.readWord (stage mem 2112 8) (2368 + 32*(8-1-k))).toNat) =
      (List.range 8).map (fun k => (MachineState.readWord mem (2112 + 32*(8-1-k))).toNat) := by
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [read_stage_member mem 2112 8 (8-1-k) (by omega)]
  simpa only [heq] using ha

theorem represents (mem : ByteArray) (a : Nat) (ha : Model.FastRepresents mem 2112 8 a) :
    Model.FastRepresents (memory mem) 2368 8 a :=
  SquarePartialClear.fastRepresents_outside _ 2368 8 a (Or.inr (by decide)) (represents_stage mem a ha)

theorem keep (mem : ByteArray) (ptr n v : Nat)
    (hd : ptr + 32*n ≤ 2048 ∨ 2624 ≤ ptr) (h : Model.FastRepresents mem ptr n v) :
    Model.FastRepresents (memory mem) ptr n v := by
  refine (Model.fastRepresents_congr (a := mem) ?_ v).1 h
  intro j hj
  rw [readWord mem (ptr+32*j) (by omega)]

end CycleSubmission.CallerMemory

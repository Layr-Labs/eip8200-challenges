import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackEndpoint

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams

open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM
open StackBlockModel StackEndpoint

theorem firstLoad_end : StackFrame.loadSite986.endPC = StackSites.leftPC 0 := rfl

theorem secondLoad_start : StackFrame.loadSite4644.startPC = StackSites.leftPC 80 := rfl

theorem secondLoad_end : StackFrame.loadSite4644.endPC = StackSites.rightPC 0 := rfl

theorem loadReturned_eq_roundEntry (s : State) (pc : UInt256) (rest : List UInt256) :
    StackLoadTrace.loadReturned s pc rest =
      StackRoundTrace.roundEntry s pc (initialWorking s).a (initialWorking s).b
        (initialWorking s).c (initialWorking s).d (initialWorking s).e rest := rfl

theorem loadEntry_eq_roundEntry (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rest : List UInt256) :
    StackLoadTrace.loadEntry s pc (StackRoundTrace.roundWords w ++ rest) =
      StackRoundTrace.roundEntry s pc w.a w.b w.c w.d w.e rest := rfl

theorem tailEntry_eq_roundEntry (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) :
    StackTail.tailEntry s left right ret rest =
      StackRoundTrace.roundEntry s (UInt256.ofNat 0x320f)
        right.a right.b right.c right.d right.e
        (StackRoundTrace.roundWords left ++ ret :: rest) := rfl

theorem firstLoad_entry (s : State) (input : ByteArray) (i : Nat) :
    StackLoadTrace.loadEntry (scheduledState s input i) StackFrame.loadSite986.startPC
      (StackFrame.frameRest input i) = StackFrame.frameLoadEntry s input i := by
  rw [StackFrame.loadSite986_startPC]
  rfl

theorem firstLoad_returned (s : State) (rest : List UInt256) :
    StackLoadTrace.loadReturned s StackFrame.loadSite986.endPC rest =
      StackRoundTrace.roundEntry s (StackSites.leftPC 0)
        (initialWorking s).a (initialWorking s).b (initialWorking s).c
        (initialWorking s).d (initialWorking s).e rest := by
  rw [firstLoad_end]
  exact loadReturned_eq_roundEntry s _ rest

theorem secondLoad_entry (s : State) (left : Compression.EvmWorking)
    (rest : List UInt256) :
    StackLoadTrace.loadEntry s StackFrame.loadSite4644.startPC
      (StackRoundTrace.roundWords left ++ rest) =
      StackRoundTrace.roundEntry s (StackSites.leftPC 80)
        left.a left.b left.c left.d left.e rest := by
  rw [secondLoad_start]
  exact loadEntry_eq_roundEntry s _ left rest

theorem secondLoad_returned (s : State) (rest : List UInt256) :
    StackLoadTrace.loadReturned s StackFrame.loadSite4644.endPC rest =
      StackRoundTrace.roundEntry s (StackSites.rightPC 0)
        (initialWorking s).a (initialWorking s).b (initialWorking s).c
        (initialWorking s).d (initialWorking s).e rest := by
  rw [secondLoad_end]
  exact loadReturned_eq_roundEntry s _ rest

theorem tailEntry_atLanePC (s : State) (left right : Compression.EvmWorking)
    (ret : UInt256) (rest : List UInt256) :
    StackTail.tailEntry s left right ret rest =
      StackRoundTrace.roundEntry s (StackSites.rightPC 80)
        right.a right.b right.c right.d right.e
        (StackRoundTrace.roundWords left ++ ret :: rest) := by
  rw [StackEndpoint.rightPC_last]
  exact tailEntry_eq_roundEntry s left right ret rest

theorem compressReturned_eq_self (s : State) (input : ByteArray) (i : Nat)
    (hpc : s.pc = UInt256.ofNat 0x643) (hstack : s.stack = driverRest input i) :
    DriverTrace.compressReturned s input i = s := by
  change {s with pc := UInt256.ofNat 0x643, stack := driverRest input i} = s
  rw [← hpc, ← hstack]

theorem resultState_returned (s : State) (input : ByteArray) (i : Nat) :
    resultState s input i = DriverTrace.compressReturned (resultState s input i) input i :=
  (compressReturned_eq_self (resultState s input i) input i rfl rfl).symm

theorem scheduled_words_memory (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (ctx : StackRunBridge.BlockContext s input i h)
    (k : Nat) (hk : k < 16) :
    MachineState.readWord (scheduledState s input i).memory (672 + 32 * k) =
      Challenge.EvmProof.Word.ofUInt32 (blockWords input i k) := by
  have hw := scheduledState_words s input i h ctx k hk
  unfold ScheduleCorrect.xValue at hw
  rw [ScheduleCorrect.xSlotWord_toNat k hk] at hw
  simpa only [Nat.mul_comm] using hw

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams

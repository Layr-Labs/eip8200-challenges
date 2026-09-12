import Challenge.Ripemd160.Submission.Proofs.Bytecode.DriverModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144PadContract
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTable144Congruence
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Bootstrap
set_option warningAsError true
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Prepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def messagePointer (i : Nat) : Nat := 1632 + DriverTrace.blockOffset i

def selectedWords (s : State) (i : Nat) : Nat → UInt256 :=
  PairedScheduleData.extractedWord s.memory (messagePointer i)

def scheduledState (s : State) (i : Nat) : State :=
  {s with
    memory := PairTable144Layout.resultMemory s.memory (selectedWords s i)
    activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}

structure Context (s : State) (input : ByteArray) (i : Nat) : Prop where
  calldata : s.executionEnv.calldata = input
  messageBlock : ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat (messagePointer i))
    (Padding.paddedMessage input) (DriverTrace.blockOffset i)

def driverRest (input : ByteArray) (i : Nat) (rho : List UInt256) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input] ++ rho

def entryState (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 510
    stack := UInt256.ofNat (messagePointer i) ::
      PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho}

def readyState (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) : State :=
  {scheduledState s i with
    pc := UInt256.ofNat 1129
    stack := Table144Bootstrap.resultStack (Word.ofUInt32 h.h0) (Word.ofUInt32 h.h1)
      (Word.ofUInt32 h.h2) (Word.ofUInt32 h.h3) (Word.ofUInt32 h.h4) (driverRest input i rho)}

theorem messagePointer_lower (i : Nat) : 1632 ≤ messagePointer i := by
  simp only [messagePointer]
  omega

theorem messagePointer_aligned (i : Nat) : messagePointer i % 32 = 0 := by
  unfold messagePointer DriverTrace.blockOffset
  omega

theorem messagePointer_bound (input : ByteArray) (hfit : input.size < 2^64)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    messagePointer i + 64 < 2^256 := by
  have hp := Padding.paddedLength_lt input.size
  have heq := DriverTrace.paddedLength_eq_blockCount input
  have hoff : DriverTrace.blockOffset i < Padding.paddedLength input.size := by
    unfold DriverTrace.blockOffset
    omega
  norm_num [messagePointer] at hfit ⊢
  omega

theorem blockOffsetWord_toNat (input : ByteArray) (hfit : input.size < 2^64)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    (DriverTrace.blockOffsetWord i).toNat = DriverTrace.blockOffset i := by
  have hb := messagePointer_bound input hfit i hi
  unfold messagePointer at hb
  rw [DriverTrace.blockOffsetWord, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem scheduled_active (s : State) (input : ByteArray) (i : Nat)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input) :
    53 ≤ (scheduledState s i).activeWords.toNat :=
  PairTable144Active.loaded_active_ge53 s (messagePointer i)
    (messagePointer_lower i) (messagePointer_bound input hfit i hi)

theorem scheduled_memory_calldata (s : State) (input : ByteArray) (i : Nat)
    (hfit : input.size < 2^64) (hi : i < DriverTrace.blockCount input)
    (ctx : Context s input i) (hhit : input.size = DriverTrace.blockOffset i) :
    PairTable144Pad.resultMemory s.memory (UInt256.ofNat s.executionEnv.calldata.size) =
      (scheduledState s i).memory := by
  rw [ctx.calldata, PairTable144Pad.resultMemory_eq_table]
  apply PairTable144Layout.resultMemory_congr
  intro k hk
  symm
  apply PairTable144Pad.extracted_words s.memory input (messagePointer i)
    hfit (by rw [hhit, DriverTrace.blockOffset]; omega)
    (messagePointer_bound input hfit i hi) _ k hk
  rw [hhit]
  exact ctx.messageBlock

#print axioms scheduled_memory_calldata
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144Prepare

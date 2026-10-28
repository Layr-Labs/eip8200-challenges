import Challenge.Ripemd160.Submission.Local20261028.FirstSpec
import Challenge.Ripemd160.Submission.Local20261028.NormalGas
set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalIteration
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open NormalPrepare

theorem expected_word (m : ByteArray) (p i : Nat) (hi : i < 16) (hb : p+64 < 2^256) :
    ScheduleCorrect.expectedWord m (UInt256.ofNat p) i =
      Word.ofUInt32 (Crypto.Ripemd160.readLE32 m (p+4*i)) := by
  have hp : Schedule.loadOffsetWord (UInt256.ofNat p) i = UInt256.ofNat (p+4*i) := by
    apply Word.word_ext
    rw [PairedScheduleData.loadOffsetWord_toNat _ _ hi hb, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
  change Word.mask32 (Schedule.readLEWord m (Schedule.loadOffsetWord (UInt256.ofNat p) i)) = _
  rw [hp]
  exact WordReader.mask32_readLEWord_eq_readLE32 _ _ (by omega)

theorem block_congr (a b : ByteArray) (p : Nat) (bs : ByteArray) (off : Nat)
    (hp : 1040 ≤ p) (hb : p+64 < 2^256)
    (hmem : ∀ j, 1040 ≤ j → a[j]?.getD 0 = b[j]?.getD 0)
    (hm : ScheduleCorrect.MessageBlockAt b (UInt256.ofNat p) bs off) :
    ScheduleCorrect.MessageBlockAt a (UInt256.ofNat p) bs off := by
  intro i hi
  rw [expected_word a p i hi hb, ← hm i hi, expected_word b p i hi hb]
  congr 1
  exact FirstSpec.readLE32_congr _ _ _ _ (fun j _ => hmem _ (by omega))

def states (s : State) (p : Nat) : Nat → State
  | 0 => s
  | n+1 => scheduled (states s p n) (p+64*n)
def hashes (s : State) (p : Nat) (h : Compression.HashState) : Nat → Compression.HashState
  | 0 => h
  | n+1 => CoreFunctional.result (states s p (n+1)).memory (hashes s p h n)

theorem outside (s : State) (p n a : Nat) (ha : 1040 ≤ a) :
    (states s p n).memory[a]?.getD 0 = s.memory[a]?.getD 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (NormalPrepare.outside (states s p n) (p+64*n) a ha).trans ih

theorem clear (s : State) (p n : Nat) (hz : Clear s.memory) : Clear (states s p n).memory := by
  induction n with
  | zero => exact hz
  | succ n ih => exact NormalPrepare.clear _ _ ih

theorem executionEnv (s : State) (p n : Nat) : (states s p n).executionEnv = s.executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem halt (s : State) (p n : Nat) : (states s p n).halt = s.halt := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem callStack (s : State) (p n : Nat) : (states s p n).callStack = s.callStack := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem message_block (s : State) (p n q : Nat) (bs : ByteArray) (off : Nat)
    (hq : 1040 ≤ q) (hb : q+64 < 2^256)
    (hm : ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat q) bs off) :
    ScheduleCorrect.MessageBlockAt (states s p n).memory (UInt256.ofNat q) bs off :=
  block_congr _ _ _ _ _ hq hb (outside s p n) hm

/-- Repeated ordinary blocks preserve every future message block and implement
    the specification's complete fold for any finite number of blocks. -/
theorem hash_spec (s : State) (p off count : Nat) (bs : ByteArray) (h : Compression.HashState)
    (hp : 1056 ≤ p) (hb : p+64*count < 2^256) (hz : Clear s.memory)
    (hm : ∀ i, i < count → ScheduleCorrect.MessageBlockAt s.memory (UInt256.ofNat (p+64*i)) bs (off+64*i)) :
    CompressionCorrect.hashArray (hashes s p h count) =
      SpecBridge.absorbBlocks (CompressionCorrect.hashArray h) bs off count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hbound : p+64*count+64 < 2^256 := by omega
    have he := NormalMessage.result_compressBlock (states s p count) (p+64*count) bs (off+64*count)
      (hashes s p h count) hbound (clear s p count hz)
      (message_block s p count (p+64*count) bs (off+64*count) (by omega) hbound (hm count (by omega)))
    change CompressionCorrect.hashArray (CoreFunctional.result (scheduled (states s p count) (p+64*count)).memory (hashes s p h count)) = _
    rw [he, ih (by omega) (fun i hi => hm i (by omega)), SpecBridge.absorbBlocks_succ]
    congr 1
    omega

def gasSteps_block (s : State) (p i : Nat) (h : Compression.HashState) (limit : UInt256) (rho : List UInt256)
    (hs : rho.length ≤ 890) (hr : s.halt = .Running) (hp : 1056 ≤ p) (hb : p+64*i+64 < 2^256)
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (hf : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
      {states s p i with pc := UInt256.ofNat 462, stack := StaggerPersistentFrame.frame (hashes s p h i) (UInt256.ofNat (p+64*i)) limit (masks rho)}
      {states s p (i+1) with pc := UInt256.ofNat 4578, stack := Word.ofUInt32 (hashes s p h i).h2 :: StaggerPersistentFrame.frame (hashes s p h (i+1)) (UInt256.ofNat (p+64*i)) limit (masks rho)} := by
  apply NormalGas.gasSteps _ _ _ _ _ hs (by rw [halt]; exact hr) (by omega) hb
  · rw [executionEnv]; exact hc
  · change (states s p i).executionEnv.fork = .Osaka
    rw [executionEnv]; exact hf
  · rw [executionEnv]; exact hnp
#print axioms message_block
#print axioms hash_spec
#print axioms gasSteps_block
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.NormalIteration

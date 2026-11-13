import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryMemory
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryCertificate
import Challenge.Ripemd160.Submission.Local20261028.PrepBiasedBytes
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.OrdinaryBytes
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open RipemdMemoryBridge20261028 PairedScheduleMemory OrdinaryCertificate

def biased (m : ByteArray) : UInt256 :=
  UInt256.add (UInt256.ofNat (BiasedBytes.key * 2^144)) (MachineState.readWord (fanMemory m) 134)
def value (m : ByteArray) : Symbol → UInt8
  | .inl n => valuation m n
  | .inr j => PoolByte.byte (biased m) j
def Matches (memory : ByteArray) (symbols : Nat → Symbol) (m : ByteArray) : Prop :=
  ∀ a, memory[a]?.getD 0 = value m (symbols a)
def sourceWord (m : ByteArray) (a : Nat) : UInt256 :=
  if a=134 then biased m else MachineState.readWord (fanMemory m) a
def store (m memory : ByteArray) (w : Nat × Nat) : ByteArray :=
  writeWord memory w.1 (sourceWord m w.2)
def resultMemory (m : ByteArray) : ByteArray :=
  OrdinaryCertificate.plan.foldl (store m) (fanMemory m)

theorem source_byte (m : ByteArray)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0)
    (a j : Nat) (hj : j<32) :
    PoolByte.byte (sourceWord m a) j = value m (OrdinaryCertificate.source a j) := by
  by_cases ha : a=134
  · subst a
    by_cases hr : 9 ≤ j ∧ j<14
    · simp only [sourceWord, OrdinaryCertificate.source, eq_self, ite_true,
        true_and, if_pos hr, value]
    · have h8 : PoolByte.byte (MachineState.readWord (fanMemory m) 134) 8 = 0 := by
        rw [PoolByte.read _ _ _ (by decide), actual_fan_matches m hz]
        rfl
      have h9 : PoolByte.byte (MachineState.readWord (fanMemory m) 134) 9 = 0 := by
        rw [PoolByte.read _ _ _ (by decide), actual_fan_matches m hz]
        rfl
      simp only [sourceWord, OrdinaryCertificate.source, eq_self, ite_true,
        true_and, if_neg hr, value, biased]
      rw [BiasedBytes.word_byte_unchanged _ h8 h9 j hj (by omega), PoolByte.read _ _ _ hj]
      exact actual_fan_matches m hz _
  · simp only [sourceWord, if_neg ha, OrdinaryCertificate.source,
      if_neg (by tauto : ¬ (a=134 ∧ 9 ≤ j ∧ j<14)), value]
    rw [PoolByte.read _ _ _ hj]
    exact actual_fan_matches m hz _

theorem store_matches (m memory : ByteArray) (symbols : Nat → Symbol)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0)
    (hm : Matches memory symbols m) (w : Nat × Nat) :
    Matches (store m memory w) (paint symbols w) m := by
  intro a
  rw [store, write_getD]
  unfold paint
  split_ifs with h
  · exact source_byte m hz w.2 (a-w.1) (by omega)
  · exact hm a

theorem fold_matches (m memory : ByteArray) (symbols : Nat → Symbol)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0)
    (hm : Matches memory symbols m) (ws : List (Nat × Nat)) :
    Matches (ws.foldl (store m) memory) (ws.foldl paint symbols) m := by
  induction ws generalizing memory symbols with
  | nil => exact hm
  | cons w ws ih => exact ih _ _ (store_matches m memory symbols hz hm w)

theorem result_matches (m : ByteArray)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, m[a]?.getD 0 = 0) :
    Matches (resultMemory m) layout m := by
  apply fold_matches m (fanMemory m) _ hz
  exact actual_fan_matches m hz

theorem model_exact (s : State) : OrdinaryMemory.memory36 s = resultMemory s.memory := by
  rfl

theorem actual_bytes (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (a : Nat) :
    (OrdinaryTable.result7 s x rho).memory[a]?.getD 0 = value s.memory (layout a) := by
  rw [OrdinaryMemory.actual_memory, model_exact]
  exact result_matches s.memory hz a

theorem preserves_zeros (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (a : Nat) (ha : a ∈ RipemdTableOrder20261027.clearAddresses) :
    (OrdinaryTable.result7 s x rho).memory[a]?.getD 0 = 0 := by
  rw [actual_bytes s x rho hz, OrdinaryCertificate.clear_sources a ha]
  rfl
#print axioms source_byte
#print axioms model_exact
#print axioms actual_bytes
#print axioms preserves_zeros
end RipemdSubmission20261101.OrdinaryBytes

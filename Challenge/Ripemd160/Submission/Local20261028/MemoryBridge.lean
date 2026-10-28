import Challenge.Ripemd160.Submission.Local20261028.GeneralCertificate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144WordRound

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdMemoryBridge20261028
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedScheduleMemory
open RipemdTableOrder20261027

def Matches (memory : ByteArray) (symbols : Nat → Nat) (value : Nat → UInt8) : Prop :=
  ∀ a, memory[a]?.getD 0 = value (symbols a)

theorem write_getD (m : ByteArray) (address : Nat) (word : UInt256) (a : Nat) :
    (writeWord m address word)[a]?.getD 0 =
      if address ≤ a ∧ a < address+32 then PoolByte.byte word (a-address) else m[a]?.getD 0 := by
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  split_ifs with h
  · exact PoolByte.encoded word (a-address) (by omega)
  · rfl

def copy (m : ByteArray) (dest source : Nat) : ByteArray :=
  writeWord m dest (MachineState.readWord m source)

def copied (symbols : Nat → Nat) (dest source : Nat) (a : Nat) : Nat :=
  if dest ≤ a ∧ a < dest+32 then symbols (source+(a-dest)) else symbols a

theorem copy_matches (m : ByteArray) (symbols : Nat → Nat) (value : Nat → UInt8)
    (hm : Matches m symbols value) (dest source : Nat) :
    Matches (copy m dest source) (copied symbols dest source) value := by
  intro a
  rw [copy, write_getD]
  unfold copied
  split_ifs with h
  · rw [PoolByte.read _ _ _ (by omega)]
    exact hm _
  · exact hm _

def fanMemory (m : ByteArray) : ByteArray :=
  copy (copy (copy (copy m 128 146) 196 178) 218 236) 286 268

theorem fan_symbols (symbols : Nat → Nat) (a : Nat) :
    copied (copied (copied (copied symbols 128 146) 196 178) 218 236) 286 268 a =
      if 286 ≤ a ∧ a < 318 then symbols (a-18)
      else if 218 ≤ a ∧ a < 250 then symbols (a+18)
      else if 196 ≤ a ∧ a < 228 then symbols (a-18)
      else if 128 ≤ a ∧ a < 160 then symbols (a+18) else symbols a := by
  simp only [copied]
  split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega)

theorem fan_matches (m : ByteArray) (value : Nat → UInt8)
    (hm : Matches m RipemdTableOrder20261027.initial value) :
    Matches (fanMemory m) RipemdTableOrder20261027.fan value := by
  have h := copy_matches _ _ value
    (copy_matches _ _ value (copy_matches _ _ value (copy_matches _ _ value hm 128 146)
      196 178) 218 236) 286 268
  intro a
  have ha := h a
  rw [fan_symbols] at ha
  exact ha

theorem pair_byte (j : Nat) (hj : j < 32) :
    PoolByte.byte Paired144WordRound.pairWord j = if RipemdTableOrder20261027.laneByte j then 255 else 0 := by
  have h : ∀ j : Fin 32, PoolByte.byte Paired144WordRound.pairWord j.val =
      if RipemdTableOrder20261027.laneByte j.val then 255 else 0 := by decide +kernel
  exact h ⟨j,hj⟩

def sourceWord (sources : ByteArray) (w : RipemdTableOrder20261027.Write) : UInt256 :=
  if w.2.2.2 then UInt256.land (MachineState.readWord sources w.2.2.1)
    Paired144WordRound.pairWord else MachineState.readWord sources w.2.2.1

def store (sources m : ByteArray) (w : RipemdTableOrder20261027.Write) : ByteArray :=
  writeWord m w.2.1 (sourceWord sources w)

def resultMemory (sources : ByteArray) (ws : List RipemdTableOrder20261027.Write) : ByteArray :=
  ws.foldl (store sources) sources

theorem source_byte (sources : ByteArray) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hz : value 0 = 0)
    (w : RipemdTableOrder20261027.Write) (j : Nat) (hj : j < 32) :
    PoolByte.byte (sourceWord sources w) j = value (RipemdTableOrder20261027.sourceByte w j) := by
  rcases w with ⟨pc, dest, source, masked⟩
  cases masked
  · simpa only [sourceWord, RipemdTableOrder20261027.sourceByte, Bool.false_eq_true, if_false, Bool.false_and]
      using (PoolByte.read sources source j hj).trans (hs _)
  · simp only [sourceWord, RipemdTableOrder20261027.sourceByte, if_true, Bool.true_and]
    rw [PoolByte.land, pair_byte j hj, PoolByte.read _ _ _ hj]
    cases hl : RipemdTableOrder20261027.laneByte j <;> simp [hl, hz]
    exact hs _

theorem store_matches (sources m : ByteArray) (symbols : Nat → Nat) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hm : Matches m symbols value) (hz : value 0 = 0)
    (w : RipemdTableOrder20261027.Write) : Matches (store sources m w) (RipemdTableOrder20261027.applyWrite symbols w) value := by
  intro a
  rw [store, write_getD]
  unfold RipemdTableOrder20261027.applyWrite
  split_ifs with h
  · exact source_byte sources value hs hz w (a-w.2.1) (by omega)
  · exact hm _

theorem fold_matches (sources m : ByteArray) (symbols : Nat → Nat) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hm : Matches m symbols value) (hz : value 0 = 0)
    (ws : List RipemdTableOrder20261027.Write) :
    Matches (ws.foldl (store sources) m) (ws.foldl RipemdTableOrder20261027.applyWrite symbols) value := by
  induction ws generalizing m symbols with
  | nil => exact hm
  | cons w ws ih =>
    exact ih _ _ (store_matches sources m symbols value hs hm hz w)

theorem result_matches (sources : ByteArray) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hz : value 0 = 0) (ws : List RipemdTableOrder20261027.Write) :
    Matches (resultMemory sources ws) (RipemdTableOrder20261027.result ws) value :=
  fold_matches sources sources RipemdTableOrder20261027.fan value hs hs hz ws

theorem projected_reads (sources : ByteArray) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hz : value 0 = 0) (l : RipemdTableOrder20261027.Load) (hl : l ∈ RipemdTableOrder20261027.loads)
    (j : Nat) (hj : j ∈ RipemdTableOrder20261027.offsets l.2.2.2) :
    (resultMemory sources RipemdTableOrder20261027.plan)[l.2.1+j]?.getD 0 =
      (resultMemory sources RipemdTableOrder20261027.selected)[l.2.2.1+j]?.getD 0 := by
  rw [result_matches sources value hs hz RipemdTableOrder20261027.plan _, result_matches sources value hs hz RipemdTableOrder20261027.selected _]
  exact RipemdTableOrder20261027.projected_under_every_assignment value l hl j hj

theorem preserved_zeros (sources : ByteArray) (value : Nat → UInt8)
    (hs : Matches sources RipemdTableOrder20261027.fan value) (hz : value 0 = 0) (a : Nat) (ha : a ∈ RipemdTableOrder20261027.clearAddresses) :
    (resultMemory sources RipemdTableOrder20261027.selected)[a]?.getD 0 = 0 := by
  rw [result_matches sources value hs hz RipemdTableOrder20261027.selected]
  exact RipemdTableOrder20261027.next_entry_under_every_assignment value hz a ha

#print axioms fan_matches
#print axioms result_matches
#print axioms projected_reads
#print axioms preserved_zeros
end RipemdMemoryBridge20261028

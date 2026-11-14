import Challenge.Ripemd160.Submission.Local20261028.PrepFirstMemory
import Challenge.Ripemd160.Submission.Local20261028.PrepOrdinaryReads
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace RipemdSubmission20261101.FirstLayout
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof Challenge.EvmProof.Memory
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
open RipemdMemoryBridge20261028 PairedScheduleMemory GeneralMessageLayout
def fixedHigh : Array Nat := #[0,0,0,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,0,0]
def initial (a : Nat) : Nat :=
  if 162 ≤ a ∧ a < 194 then fixedHigh[a-162]!
  else if 252 ≤ a ∧ a < 284 then 1+((a-252)/4)*4+3-(a-252)%4
  else if 1056 ≤ a ∧ a < 1088 then 1+a-1056
  else if a < 1088 then 0 else 1000+a

def value (m : ByteArray) (symbol : Nat) : UInt8 :=
  if symbol = 0 then 0
  else if symbol = 33 then 1
  else if symbol = 34 then 128
  else if symbol ≤ 32 then m[1056+symbol-1]?.getD 0
  else if 1000 ≤ symbol then m[symbol-1000]?.getD 0
  else UInt8.ofNat (symbol-256)


def written (symbols : Nat → Nat) (address size : Nat) (source : Nat → Nat) (a : Nat) : Nat :=
  if address ≤ a ∧ a < address+size then source (a-address) else symbols a

theorem write_matches (m : ByteArray) (symbols : Nat → Nat) (v : Nat → UInt8)
    (hm : Matches m symbols v) (address : Nat) (word : UInt256) (source : Nat → Nat)
    (hw : ∀ j, j < 32 → PoolByte.byte word j = v (source j)) :
    Matches (writeWord m address word) (written symbols address 32 source) v := by
  intro a
  rw [write_getD]
  unfold written
  split_ifs with ha
  · exact hw _ (by omega)
  · exact hm a

theorem write_bytes_matches (m bytes : ByteArray) (symbols : Nat → Nat) (v : Nat → UInt8)
    (hm : Matches m symbols v) (address size : Nat) (source : Nat → Nat)
    (hs : bytes.size = size) (hw : ∀ j, j < size → bytes[j]?.getD 0 = v (source j)) :
    Matches (MachineState.writeBytes m bytes address) (written symbols address size source) v := by
  intro a
  rw [MachineState.writeBytes_getElem?_getD, hs]
  unfold written
  split_ifs with ha
  · exact hw _ (by omega)
  · exact hm a

def symbols0 := initial
 theorem matches0 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (FirstMemory.memory0 s) symbols0 (value s.memory) := h
def symbols1 : Nat → Nat := written symbols0 218 32 (fun j => symbols0 (236+j))
theorem matches1 (s : State) (h : Matches s.memory initial (value s.memory))
    (_hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory1 s) symbols1 (value s.memory) := by
  apply write_matches _ _ _ (matches0 s h)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches0 s h _
def symbols2 : Nat → Nat := written symbols1 286 32 (fun j => symbols1 (268+j))
theorem matches2 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory2 s) symbols2 (value s.memory) := by
  apply write_matches _ _ _ (matches1 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches1 s h hc _
def literal3 : Array Nat := #[34]
def symbols3 : Nat → Nat := written symbols2 147 1 (fun j => literal3[j]!)
theorem matches3 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory3 s) symbols3 (value s.memory) := by
  apply write_bytes_matches _ _ _ _ (matches2 s h hc) 147 1 (fun j => literal3[j]!) rfl
  intro j hj
  have : j=0 := by omega
  subst j
  rfl
def literal4 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal4_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 1329227995784915872903807060280344576) j = value m literal4[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 1329227995784915872903807060280344576) j.val = value m literal4[j.val]! := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def symbols4 : Nat → Nat := written symbols3 216 32 (fun j => literal4[j]!)
theorem matches4 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory4 s) symbols4 (value s.memory) := by
  apply write_matches _ _ _ (matches3 s h hc)
  exact literal4_bytes s.memory
def literal5 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal5_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 0) j = value m literal5[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 0) j.val = value m literal5[j.val]! := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def symbols5 : Nat → Nat := written symbols4 252 32 (fun j => literal5[j]!)
theorem matches5 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory5 s) symbols5 (value s.memory) := by
  apply write_matches _ _ _ (matches4 s h hc)
  exact literal5_bytes s.memory
def literal6 : Array Nat := #[34]
def symbols6 : Nat → Nat := symbols5
theorem matches6 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory6 s) symbols6 (value s.memory) :=
  matches5 s h hc
def literal7 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 425, 339, 509, 462, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34]
theorem literal7_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 63353160442001178124083124585511767107666197511929984) j = value m literal7[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 63353160442001178124083124585511767107666197511929984) j.val = value m literal7[j.val]! := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def symbols7 : Nat → Nat := written symbols6 936 32 (fun j => literal7[j]!)
theorem matches7 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory7 s) symbols7 (value s.memory) := by
  apply write_matches _ _ _ (matches6 s h hc)
  exact literal7_bytes s.memory
def symbols8 : Nat → Nat := written symbols7 18 32 (fun j => symbols2 (266+j))
theorem matches8 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory8 s) symbols8 (value s.memory) := by
  apply write_matches _ _ _ (matches7 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols9 : Nat → Nat := written symbols8 108 32 (fun j => symbols2 (258+j))
theorem matches9 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory9 s) symbols9 (value s.memory) := by
  apply write_matches _ _ _ (matches8 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols10 : Nat → Nat := written symbols9 90 32 (fun j => symbols2 (224+j))
theorem matches10 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory10 s) symbols10 (value s.memory) := by
  apply write_matches _ _ _ (matches9 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols11 : Nat → Nat := written symbols10 72 32 (fun j => symbols2 (258+j))
theorem matches11 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory11 s) symbols11 (value s.memory) := by
  apply write_matches _ _ _ (matches10 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def literal12 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal12_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 309485009821345068724781056) j = value m literal12[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 309485009821345068724781056) j.val = value m literal12[j.val]! := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def symbols12 : Nat → Nat := written symbols11 54 32 (fun j => literal12[j]!)
theorem matches12 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory12 s) symbols12 (value s.memory) := by
  apply write_matches _ _ _ (matches11 s h hc)
  exact literal12_bytes s.memory
def symbols13 : Nat → Nat := written symbols12 324 32 (fun j => symbols2 (232+j))
theorem matches13 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory13 s) symbols13 (value s.memory) := by
  apply write_matches _ _ _ (matches12 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols14 : Nat → Nat := written symbols13 360 32 (fun j => symbols2 (258+j))
theorem matches14 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory14 s) symbols14 (value s.memory) := by
  apply write_matches _ _ _ (matches13 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols15 : Nat → Nat := written symbols14 414 32 (fun j => symbols2 (258+j))
theorem matches15 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory15 s) symbols15 (value s.memory) := by
  apply write_matches _ _ _ (matches14 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols16 : Nat → Nat := written symbols15 396 32 (fun j => symbols2 (266+j))
theorem matches16 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory16 s) symbols16 (value s.memory) := by
  apply write_matches _ _ _ (matches15 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
theorem shl112_byte (w : UInt256) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.shiftLeft w (UInt256.ofNat 112)) j =
      if j < 18 then PoolByte.byte w (j+14) else 0 := by
  have hshl : (UInt256.shiftLeft w (UInt256.ofNat 112)).toNat = w.toNat * 2^112 % 2^256 := by
    unfold UInt256.shiftLeft
    have hshift : (UInt256.ofNat 112).toNat = 112 := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]; rfl
    rw [if_neg (by omega), hshift, Challenge.EvmProof.Word.word_toNat_ofNat,
      show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod, Nat.shiftLeft_eq]
  apply UInt8.toNat_inj.mp
  rw [PoolByte.byte_toNat, hshl]
  split_ifs with h
  · have e1 : (2:Nat)^256 = 2^(8*(31-j)) * 2^(8*j+8) := by
      rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
    have e2 : (2:Nat)^(8*(31-j)) = 2^(8*(31-(j+14))) * 2^112 := by
      rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
    have e3 : 256 ∣ (2:Nat)^(8*j+8) :=
      ⟨2^(8*j), by rw [show 8*j+8 = 8 + 8*j by omega, Nat.pow_add]⟩
    rw [PoolByte.byte_toNat, e1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ e3, e2,
      Nat.mul_div_mul_right _ _ (by positivity)]
  · have hd : 2^(8*(31-j)) * 2^8 ∣ w.toNat * 2^112 % 2^256 := by
      rw [← Nat.pow_add]
      apply (Nat.dvd_mod_iff (Nat.pow_dvd_pow 2 (by omega))).mpr
      exact Dvd.dvd.mul_left (Nat.pow_dvd_pow 2 (by omega)) _
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
    simp
def symbols17 : Nat → Nat :=
  written (written symbols16 482 32 (fun j => if j < 18 then symbols2 (262+(j+14)) else 0))
    787 1 (fun j => literal6[j]!)
theorem matches17 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory17 s) symbols17 (value s.memory) := by
  refine write_bytes_matches _ _ _ _ ?hm 787 1 (fun j => literal6[j]!) rfl ?hw
  case hw =>
    intro j hj
    have : j=0 := by omega
    subst j
    rfl
  case hm =>
    apply write_matches _ _ _ (matches16 s h hc)
    intro j hj
    rw [shl112_byte _ j hj]
    split_ifs with hjr
    · rw [PoolByte.read _ _ _ (by omega)]
      exact matches2 s h hc _
    · simp [value]
def symbols18 : Nat → Nat := written symbols17 522 32 (fun j => symbols2 (228+j))
theorem matches18 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory18 s) symbols18 (value s.memory) := by
  apply write_matches _ _ _ (matches17 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols19 : Nat → Nat := written symbols18 540 32 (fun j => symbols2 (224+j))
theorem matches19 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory19 s) symbols19 (value s.memory) := by
  apply write_matches _ _ _ (matches18 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols20 : Nat → Nat := written symbols19 558 32 (fun j => symbols2 (228+j))
theorem matches20 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory20 s) symbols20 (value s.memory) := by
  apply write_matches _ _ _ (matches19 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols21 : Nat → Nat := written symbols20 684 32 (fun j => symbols2 (266+j))
theorem matches21 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory21 s) symbols21 (value s.memory) := by
  apply write_matches _ _ _ (matches20 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def literal22 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem basis_byte (j : Fin 122) :
    (MachineState.readPadded Challenge.Ripemd160.Benchmark.bytecode 10426 122)[j.val]?.getD 0 =
      (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])[j.val]?.getD 0 := by
  rw [readPadded_getElem?_getD, if_pos j.isLt]
  change (Challenge.Ripemd160.Benchmark.bytecode.data[10426+j.val]?).getD 0 = _
  rw [← Array.getElem?_toList, RipemdSubmissionTables20261028.CandidateBytes.exact_list]
  have he : 10426+j.val = 10368+(58+j.val) := by omega
  rw [he, ← List.getElem?_drop, RipemdSubmissionTables20261028.CandidateBytes.drop162]
  fin_cases j <;> rfl
 theorem code_bytes (s : State) (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode)
    (j : Nat) (hj : j < 122) :
    (MachineState.readPadded s.executionEnv.code 10426 122)[j]?.getD 0 = value s.memory literal22[j]! := by
  rw [hc, basis_byte ⟨j,hj⟩]
  have h : ∀ j : Fin 122, (ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])[j.val]?.getD 0 = value s.memory literal22[j.val]! := by
    intro j; fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def symbols22 : Nat → Nat := written symbols21 576 122 (fun j => literal22[j]!)
theorem matches22 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory22 s) symbols22 (value s.memory) := by
  apply write_bytes_matches _ _ _ _ (matches21 s h hc) 576 122 (fun j => literal22[j]!) (readPadded_size _ _ _)
  exact code_bytes s hc
def symbols23 : Nat → Nat := written symbols22 738 32 (fun j => symbols2 (262+j))
theorem matches23 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory23 s) symbols23 (value s.memory) := by
  apply write_matches _ _ _ (matches22 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols24 : Nat → Nat := written symbols23 720 32 (fun j => symbols2 (262+j))
theorem matches24 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory24 s) symbols24 (value s.memory) := by
  apply write_matches _ _ _ (matches23 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
theorem shr112_byte (w : UInt256) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.shiftRight w (UInt256.ofNat 112)) j =
      if 14 ≤ j then PoolByte.byte w (j-14) else 0 := by
  apply UInt8.toNat_inj.mp
  rw [PoolByte.byte_toNat, Challenge.EvmProof.Word.shiftRight_toNat _ (by norm_num),
    Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]
  split_ifs with h
  · rw [PoolByte.byte_toNat, show 112 + 8*(31-j) = 8*(31-(j-14)) by omega]
  · have hlt : w.toNat < 2^(112 + 8*(31-j)) :=
      lt_of_lt_of_le w.val.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hlt]
    rfl
def symbols25 : Nat → Nat := written symbols24 814 32 (fun j => if 14 ≤ j then symbols2 (236+(j-14)) else 0)
theorem matches25 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory25 s) symbols25 (value s.memory) := by
  apply write_matches _ _ _ (matches24 s h hc)
  intro j hj
  rw [shr112_byte _ j hj]
  split_ifs with hjr
  · rw [PoolByte.read _ _ _ (by omega)]
    exact matches2 s h hc _
  · simp [value]
def symbols26 : Nat → Nat := written symbols25 972 32 (fun j => symbols2 (236+j))
theorem matches26 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory26 s) symbols26 (value s.memory) := by
  apply write_matches _ _ _ (matches25 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
def symbols27 : Nat → Nat := written symbols26 864 32 (fun j => symbols2 (236+j))
theorem matches27 (s : State) (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) :
    Matches (FirstMemory.memory27 s) symbols27 (value s.memory) := by
  apply write_matches _ _ _ (matches26 s h hc)
  intro j hj
  rw [PoolByte.read _ _ _ hj]
  exact matches2 s h hc _
theorem actual_bytes (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (h : Matches s.memory initial (value s.memory))
    (hc : s.executionEnv.code = Challenge.Ripemd160.Benchmark.bytecode) (a : Nat) :
    (FirstTable.result5 s x rho).memory[a]?.getD 0 = value s.memory (symbols27 a) := by
  rw [FirstMemory.actual_memory]
  exact matches27 s h hc a

theorem low_sources : ∀ slot : Fin 61, slot.val ≠ 51 → ∀ j : Fin 4,
    symbols27 (addresses[slot.val]!+28+j.val) = initial (wordAddress StaggerTableLayout.slots[slot.val]!+j.val) := by decide +kernel

theorem high_sources : ∀ i : Fin 77, ∀ j : Fin 4,
    symbols27 (addresses[StaggerTableLayout.pairIndices[i.val]!]!+10+j.val) =
      initial (wordAddress Crypto.Ripemd160.rP[i.val+3]!+j.val) := by decide +kernel

theorem barrier_sources : ∀ i : Fin 77,
    14 ≤ barriers[i.val]! ∧ barriers[i.val]! ≤ 26 ∧
    symbols27 (addresses[StaggerTableLayout.pairIndices[i.val]!]!+barriers[i.val]!) = 0 := by decide +kernel
#print axioms actual_bytes
#print axioms low_sources
#print axioms high_sources
#print axioms barrier_sources
end RipemdSubmission20261101.FirstLayout

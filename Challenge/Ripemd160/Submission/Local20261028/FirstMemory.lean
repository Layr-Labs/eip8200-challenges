import Challenge.Ripemd160.Submission.Local20261028.TableComposition
import Challenge.Ripemd160.Submission.Local20261028.MemoryBridge
import Challenge.Ripemd160.Submission.Local20261028.GeneralMessageLayout
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace RipemdMemoryBridge20261028.FirstMemory
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028
open RipemdSubmissionTables20261028
open PairedScheduleMemory

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

def written (symbols : Nat → Nat) (address : Nat) (source : Nat → Nat) (a : Nat) : Nat :=
  if address ≤ a ∧ a < address+32 then source (a-address) else symbols a

theorem write_matches (m : ByteArray) (symbols : Nat → Nat) (v : Nat → UInt8)
    (hm : Matches m symbols v) (address : Nat) (word : UInt256) (source : Nat → Nat)
    (hw : ∀ j, j < 32 → PoolByte.byte word j = v (source j)) :
    Matches (writeWord m address word) (written symbols address source) v := by
  intro a
  rw [write_getD]
  unfold written
  split_ifs with ha
  · exact hw _ (by omega)
  · exact hm _

def literal14 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal14_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 10141204801825835211973625643008) j = value m literal14[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 10141204801825835211973625643008) j.val = value m literal14[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal16 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal16_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 374144419156711147060143317175368453031918731001856) j = value m literal16[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 374144419156711147060143317175368453031918731001856) j.val = value m literal16[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal22 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34]
theorem literal22_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 2854495385411919762116571938898990272765493376) j = value m literal22[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 2854495385411919762116571938898990272765493376) j.val = value m literal22[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal23 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0]
theorem literal23_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592) j = value m literal23[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592) j.val = value m literal23[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal24 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0]
theorem literal24_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 5708990770823839524233143877797980545530986752) j = value m literal24[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 5708990770823839524233143877797980545530986752) j.val = value m literal24[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal25 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal25_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 2854495385411919762116571938898990272765493248) j = value m literal25[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 2854495385411919762116571938898990272765493248) j.val = value m literal25[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal32 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal32_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 1329227995784915872903807060280344576) j = value m literal32[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 1329227995784915872903807060280344576) j.val = value m literal32[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal33 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal33_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 309485009821345068724781056) j = value m literal33[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 309485009821345068724781056) j.val = value m literal33[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
def literal54 : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem literal54_bytes (m : ByteArray) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 0) j = value m literal54[j]! := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 0) j.val = value m literal54[j.val]! := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩

theorem low18_byte (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 22300745198530623141535718272648361505980415) j = if 14 ≤ j then 255 else 0 := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 22300745198530623141535718272648361505980415) j.val = if 14 ≤ j.val then 255 else 0 := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
theorem high18_byte (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.ofNat 115792089237316195423570985008687907853269979473343705504629955477416800419840) j = if j < 18 then 255 else 0 := by
  have h : ∀ j : Fin 32, PoolByte.byte (UInt256.ofNat 115792089237316195423570985008687907853269979473343705504629955477416800419840) j.val = if j.val < 18 then 255 else 0 := by
    intro j
    fin_cases j <;> rfl
  exact h ⟨j,hj⟩
/-- Bytes of `mask AND w` for a mask whose bytes are all-ones (kept) or zero (cleared). -/
theorem masked_bytes (m : ByteArray) (mask w : UInt256) (keep : Nat → Prop) [DecidablePred keep]
    (src : Nat → Nat)
    (hmask : ∀ j, j < 32 → PoolByte.byte mask j = if keep j then 255 else 0)
    (hw : ∀ j, j < 32 → PoolByte.byte w j = value m (src j)) (j : Nat) (hj : j < 32) :
    PoolByte.byte (UInt256.land mask w) j = value m (if keep j then src j else 0) := by
  rw [PoolByte.land, hmask j hj]
  by_cases hk : keep j
  · rw [if_pos hk, if_pos hk, ← hw j hj]
    apply UInt8.eq_of_toBitVec_eq
    exact BitVec.allOnes_and
  · rw [if_neg hk, if_neg hk, show value m 0 = 0 from rfl]
    apply UInt8.eq_of_toBitVec_eq
    exact BitVec.zero_and

def frame (continuation : UInt256) : Nat → UInt256 :=
  fun i => #[(UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)][i]!
def memory0 (s : State) : ByteArray := s.memory
def symbols0 : Nat → Nat := initial
theorem matches0 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory0 s) symbols0 (value s.memory) := h
def memory1 (s : State) : ByteArray := writeWord (memory0 s) 128 (UInt256.ofNat 10141204801825835211973625643008)
def symbols1 : Nat → Nat := written symbols0 128 (fun j => literal14[j]!)
theorem matches1 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory1 s) symbols1 (value s.memory) :=
  write_matches _ _ _ (matches0 s h) 128 _ _ (literal14_bytes s.memory)
def memory2 (s : State) : ByteArray := memory1 s
def symbols2 : Nat → Nat := symbols1
theorem matches2 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory2 s) symbols2 (value s.memory) :=
  matches1 s h
def memory3 (s : State) : ByteArray := writeWord (memory2 s) 218 (MachineState.readWord (memory2 s) 236)
def symbols3 : Nat → Nat := written symbols2 218 (fun j => symbols2 (236+j))
theorem matches3 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory3 s) symbols3 (value s.memory) :=
  write_matches _ _ _ (matches2 s h) 218 _ _ (fun j hj => (PoolByte.read (memory2 s) 236 j hj).trans (matches2 s h _))
def memory4 (s : State) : ByteArray := writeWord (memory3 s) 286 (MachineState.readWord (memory3 s) 268)
def symbols4 : Nat → Nat := written symbols3 286 (fun j => symbols3 (268+j))
theorem matches4 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory4 s) symbols4 (value s.memory) :=
  write_matches _ _ _ (matches3 s h) 286 _ _ (fun j hj => (PoolByte.read (memory3 s) 268 j hj).trans (matches3 s h _))
def state0 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10172, stack := [(UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory4 s}
theorem eq0 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result0 s (frame continuation) rho = state0 s continuation rho := by
  rfl
def memory5 (s : State) : ByteArray := writeWord (memory4 s) 18 (MachineState.readWord (memory4 s) 266)
def symbols5 : Nat → Nat := written symbols4 18 (fun j => symbols4 (266+j))
theorem matches5 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory5 s) symbols5 (value s.memory) :=
  write_matches _ _ _ (matches4 s h) 18 _ _ (fun j hj => (PoolByte.read (memory4 s) 266 j hj).trans (matches4 s h _))
def state1 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10317, stack := [(UInt256.ofNat 309485009821345068724781056), (UInt256.ofNat 1329227995784915872903807060280344576), (MachineState.readWord (memory4 s) 232), (MachineState.readWord (memory4 s) 258), (MachineState.readWord (memory4 s) 224), (MachineState.readWord (memory4 s) 228), (MachineState.readWord (memory4 s) 266), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (MachineState.readWord (memory4 s) 262), (UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory5 s}
theorem eq1 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result1 s (frame continuation) rho = state1 s continuation rho := by
  simp only [FirstTable.result1, eq0]
  rfl
def memory6 (s : State) : ByteArray := writeWord (memory5 s) 108 (MachineState.readWord (memory4 s) 258)
def symbols6 : Nat → Nat := written symbols5 108 (fun j => symbols4 (258+j))
theorem matches6 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory6 s) symbols6 (value s.memory) :=
  write_matches _ _ _ (matches5 s h) 108 _ _ (fun j hj => (PoolByte.read (memory4 s) 258 j hj).trans (matches4 s h _))
def memory7 (s : State) : ByteArray := writeWord (memory6 s) 90 (MachineState.readWord (memory4 s) 224)
def symbols7 : Nat → Nat := written symbols6 90 (fun j => symbols4 (224+j))
theorem matches7 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory7 s) symbols7 (value s.memory) :=
  write_matches _ _ _ (matches6 s h) 90 _ _ (fun j hj => (PoolByte.read (memory4 s) 224 j hj).trans (matches4 s h _))
def memory8 (s : State) : ByteArray := writeWord (memory7 s) 72 (MachineState.readWord (memory4 s) 258)
def symbols8 : Nat → Nat := written symbols7 72 (fun j => symbols4 (258+j))
theorem matches8 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory8 s) symbols8 (value s.memory) :=
  write_matches _ _ _ (matches7 s h) 72 _ _ (fun j hj => (PoolByte.read (memory4 s) 258 j hj).trans (matches4 s h _))
def memory9 (s : State) : ByteArray := writeWord (memory8 s) 54 (UInt256.ofNat 309485009821345068724781056)
def symbols9 : Nat → Nat := written symbols8 54 (fun j => literal33[j]!)
theorem matches9 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory9 s) symbols9 (value s.memory) :=
  write_matches _ _ _ (matches8 s h) 54 _ _ (literal33_bytes s.memory)
def memory10 (s : State) : ByteArray := writeWord (memory9 s) 216 (UInt256.ofNat 1329227995784915872903807060280344576)
def symbols10 : Nat → Nat := written symbols9 216 (fun j => literal32[j]!)
theorem matches10 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory10 s) symbols10 (value s.memory) :=
  write_matches _ _ _ (matches9 s h) 216 _ _ (literal32_bytes s.memory)
def state2 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10335, stack := [(MachineState.readWord (memory4 s) 232), (MachineState.readWord (memory4 s) 258), (MachineState.readWord (memory4 s) 224), (MachineState.readWord (memory4 s) 228), (MachineState.readWord (memory4 s) 266), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (MachineState.readWord (memory4 s) 262), (UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory10 s}
theorem eq2 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result2 s (frame continuation) rho = state2 s continuation rho := by
  simp only [FirstTable.result2, eq1]
  rfl
def memory11 (s : State) : ByteArray := writeWord (memory10 s) 324 (MachineState.readWord (memory4 s) 232)
def symbols11 : Nat → Nat := written symbols10 324 (fun j => symbols4 (232+j))
theorem matches11 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory11 s) symbols11 (value s.memory) :=
  write_matches _ _ _ (matches10 s h) 324 _ _ (fun j hj => (PoolByte.read (memory4 s) 232 j hj).trans (matches4 s h _))
def memory12 (s : State) : ByteArray := writeWord (memory11 s) 360 (MachineState.readWord (memory4 s) 258)
def symbols12 : Nat → Nat := written symbols11 360 (fun j => symbols4 (258+j))
theorem matches12 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory12 s) symbols12 (value s.memory) :=
  write_matches _ _ _ (matches11 s h) 360 _ _ (fun j hj => (PoolByte.read (memory4 s) 258 j hj).trans (matches4 s h _))
def memory13 (s : State) : ByteArray := writeWord (memory12 s) 414 (MachineState.readWord (memory4 s) 258)
def symbols13 : Nat → Nat := written symbols12 414 (fun j => symbols4 (258+j))
theorem matches13 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory13 s) symbols13 (value s.memory) :=
  write_matches _ _ _ (matches12 s h) 414 _ _ (fun j hj => (PoolByte.read (memory4 s) 258 j hj).trans (matches4 s h _))
def memory14 (s : State) : ByteArray := writeWord (memory13 s) 396 (MachineState.readWord (memory4 s) 266)
def symbols14 : Nat → Nat := written symbols13 396 (fun j => symbols4 (266+j))
theorem matches14 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory14 s) symbols14 (value s.memory) :=
  write_matches _ _ _ (matches13 s h) 396 _ _ (fun j hj => (PoolByte.read (memory4 s) 266 j hj).trans (matches4 s h _))
def memory15 (s : State) : ByteArray := writeWord (memory14 s) 468 (UInt256.land (UInt256.ofNat 22300745198530623141535718272648361505980415) (MachineState.readWord (memory4 s) 262))
def symbols15 : Nat → Nat := written symbols14 468 (fun j => if 14 ≤ j then symbols4 (262+j) else 0)
theorem matches15 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory15 s) symbols15 (value s.memory) :=
  write_matches _ _ _ (matches14 s h) 468 _ _
    (masked_bytes s.memory _ _ (fun j => 14 ≤ j) (fun j => symbols4 (262+j)) low18_byte
      (fun j hj => (PoolByte.read (memory4 s) 262 j hj).trans (matches4 s h _)))
def state3 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10378, stack := [(MachineState.readWord (memory4 s) 224), (MachineState.readWord (memory4 s) 228), (MachineState.readWord (memory4 s) 266), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (MachineState.readWord (memory4 s) 262), (UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory15 s}
theorem eq3 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result3 s (frame continuation) rho = state3 s continuation rho := by
  simp only [FirstTable.result3, eq2]
  rfl
def memory16 (s : State) : ByteArray := writeWord (memory15 s) 522 (MachineState.readWord (memory4 s) 228)
def symbols16 : Nat → Nat := written symbols15 522 (fun j => symbols4 (228+j))
theorem matches16 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory16 s) symbols16 (value s.memory) :=
  write_matches _ _ _ (matches15 s h) 522 _ _ (fun j hj => (PoolByte.read (memory4 s) 228 j hj).trans (matches4 s h _))
def memory17 (s : State) : ByteArray := writeWord (memory16 s) 540 (MachineState.readWord (memory4 s) 224)
def symbols17 : Nat → Nat := written symbols16 540 (fun j => symbols4 (224+j))
theorem matches17 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory17 s) symbols17 (value s.memory) :=
  write_matches _ _ _ (matches16 s h) 540 _ _ (fun j hj => (PoolByte.read (memory4 s) 224 j hj).trans (matches4 s h _))
def memory18 (s : State) : ByteArray := writeWord (memory17 s) 558 (MachineState.readWord (memory4 s) 228)
def symbols18 : Nat → Nat := written symbols17 558 (fun j => symbols4 (228+j))
theorem matches18 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory18 s) symbols18 (value s.memory) :=
  write_matches _ _ _ (matches17 s h) 558 _ _ (fun j hj => (PoolByte.read (memory4 s) 228 j hj).trans (matches4 s h _))
def memory19 (s : State) : ByteArray := writeWord (memory18 s) 684 (UInt256.land (UInt256.ofNat 22300745198530623141535718272648361505980415) (MachineState.readWord (memory4 s) 266))
def symbols19 : Nat → Nat := written symbols18 684 (fun j => if 14 ≤ j then symbols4 (266+j) else 0)
theorem matches19 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory19 s) symbols19 (value s.memory) :=
  write_matches _ _ _ (matches18 s h) 684 _ _
    (masked_bytes s.memory _ _ (fun j => 14 ≤ j) (fun j => symbols4 (266+j)) low18_byte
      (fun j hj => (PoolByte.read (memory4 s) 266 j hj).trans (matches4 s h _)))
def memory20 (s : State) : ByteArray := writeWord (memory19 s) 756 (UInt256.ofNat 2854495385411919762116571938898990272765493376)
def symbols20 : Nat → Nat := written symbols19 756 (fun j => literal22[j]!)
theorem matches20 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory20 s) symbols20 (value s.memory) :=
  write_matches _ _ _ (matches19 s h) 756 _ _ (literal22_bytes s.memory)
def memory21 (s : State) : ByteArray := writeWord (memory20 s) 738 (MachineState.readWord (memory4 s) 262)
def symbols21 : Nat → Nat := written symbols20 738 (fun j => symbols4 (262+j))
theorem matches21 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory21 s) symbols21 (value s.memory) :=
  write_matches _ _ _ (matches20 s h) 738 _ _ (fun j hj => (PoolByte.read (memory4 s) 262 j hj).trans (matches4 s h _))
def state4 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10424, stack := [(MachineState.readWord (memory4 s) 262), (UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory21 s}
theorem eq4 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result4 s (frame continuation) rho = state4 s continuation rho := by
  simp only [FirstTable.result4, eq3]
  rfl
def memory22 (s : State) : ByteArray := writeWord (memory21 s) 720 (MachineState.readWord (memory4 s) 262)
def symbols22 : Nat → Nat := written symbols21 720 (fun j => symbols4 (262+j))
theorem matches22 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory22 s) symbols22 (value s.memory) :=
  write_matches _ _ _ (matches21 s h) 720 _ _ (fun j hj => (PoolByte.read (memory4 s) 262 j hj).trans (matches4 s h _))
def memory23 (s : State) : ByteArray := writeWord (memory22 s) 828 (UInt256.land (UInt256.ofNat 115792089237316195423570985008687907853269979473343705504629955477416800419840) (MachineState.readWord (memory4 s) 236))
def symbols23 : Nat → Nat := written symbols22 828 (fun j => if j < 18 then symbols4 (236+j) else 0)
theorem matches23 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory23 s) symbols23 (value s.memory) :=
  write_matches _ _ _ (matches22 s h) 828 _ _
    (masked_bytes s.memory _ _ (fun j => j < 18) (fun j => symbols4 (236+j)) high18_byte
      (fun j hj => (PoolByte.read (memory4 s) 236 j hj).trans (matches4 s h _)))
def memory24 (s : State) : ByteArray := writeWord (memory23 s) 972 (MachineState.readWord (memory4 s) 236)
def symbols24 : Nat → Nat := written symbols23 972 (fun j => symbols4 (236+j))
theorem matches24 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory24 s) symbols24 (value s.memory) :=
  write_matches _ _ _ (matches23 s h) 972 _ _ (fun j hj => (PoolByte.read (memory4 s) 236 j hj).trans (matches4 s h _))
def memory25 (s : State) : ByteArray := writeWord (memory24 s) 252 (UInt256.ofNat 0)
def symbols25 : Nat → Nat := written symbols24 252 (fun j => literal54[j]!)
theorem matches25 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory25 s) symbols25 (value s.memory) :=
  write_matches _ _ _ (matches24 s h) 252 _ _ (literal54_bytes s.memory)
def memory26 (s : State) : ByteArray := memory25 s
def symbols26 : Nat → Nat := symbols25
theorem matches26 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory26 s) symbols26 (value s.memory) :=
  matches25 s h
def state5 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10476, stack := [(UInt256.ofNat 2854495385411919762116571938898990272765493248), (UInt256.ofNat 5708990770823839524233143877797980545530986752), (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592), (MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory26 s}
theorem eq5 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result5 s (frame continuation) rho = state5 s continuation rho := by
  simp only [FirstTable.result5, eq4]
  rfl
def memory27 (s : State) : ByteArray := writeWord (memory26 s) 576 (UInt256.ofNat 2854495385411919762116571938898990272765493248)
def symbols27 : Nat → Nat := written symbols26 576 (fun j => literal25[j]!)
theorem matches27 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory27 s) symbols27 (value s.memory) :=
  write_matches _ _ _ (matches26 s h) 576 _ _ (literal25_bytes s.memory)
def memory28 (s : State) : ByteArray := writeWord (memory27 s) 630 (UInt256.ofNat 5708990770823839524233143877797980545530986752)
def symbols28 : Nat → Nat := written symbols27 630 (fun j => literal24[j]!)
theorem matches28 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory28 s) symbols28 (value s.memory) :=
  write_matches _ _ _ (matches27 s h) 630 _ _ (literal24_bytes s.memory)
def memory29 (s : State) : ByteArray := writeWord (memory28 s) 612 (UInt256.ofNat 24519928653854221733733552434404946937899827054449262592)
def symbols29 : Nat → Nat := written symbols28 612 (fun j => literal23[j]!)
theorem matches29 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory29 s) symbols29 (value s.memory) :=
  write_matches _ _ _ (matches28 s h) 612 _ _ (literal23_bytes s.memory)
def memory30 (s : State) : ByteArray := memory29 s
def symbols30 : Nat → Nat := symbols29
theorem matches30 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory30 s) symbols30 (value s.memory) :=
  matches29 s h
def memory31 (s : State) : ByteArray := memory30 s
def symbols31 : Nat → Nat := symbols30
theorem matches31 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory31 s) symbols31 (value s.memory) :=
  matches30 s h
def state6 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10488, stack := [(MachineState.readWord (memory4 s) 236), (UInt256.ofNat 2854495385411919762116571938898990272765493376), (UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory31 s}
theorem eq6 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result6 s (frame continuation) rho = state6 s continuation rho := by
  simp only [FirstTable.result6, eq5]
  rfl
def memory32 (s : State) : ByteArray := writeWord (memory31 s) 864 (MachineState.readWord (memory4 s) 236)
def symbols32 : Nat → Nat := written symbols31 864 (fun j => symbols4 (236+j))
theorem matches32 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory32 s) symbols32 (value s.memory) :=
  write_matches _ _ _ (matches31 s h) 864 _ _ (fun j hj => (PoolByte.read (memory4 s) 236 j hj).trans (matches4 s h _))
def memory33 (s : State) : ByteArray := writeWord (memory32 s) 936 (UInt256.ofNat 2854495385411919762116571938898990272765493376)
def symbols33 : Nat → Nat := written symbols32 936 (fun j => literal22[j]!)
theorem matches33 (s : State) (h : Matches s.memory initial (value s.memory)) :
    Matches (memory33 s) symbols33 (value s.memory) :=
  write_matches _ _ _ (matches32 s h) 936 _ _ (literal22_bytes s.memory)
def state7 (s : State) (continuation : UInt256) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 10496, stack := [(UInt256.ofNat 158456325065422163343096938498), (UInt256.ofNat 4294967295), (UInt256.ofNat 822752278660603021055183846080144629349832214544141570168324096), (UInt256.ofNat 822752278660603021099785336477205875632903651089438293180284928), (UInt256.ofNat 1109194275457955143345843994625), (UInt256.ofNat 475368975196266490007815979009), (UInt256.ofNat 3285377520), (UInt256.ofNat 271733878), (UInt256.ofNat 2562383102), (UInt256.ofNat 4023233417), (UInt256.ofNat 1732584193), (UInt256.ofNat 1056), continuation, (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255)] ++ rho, memory := memory33 s}
theorem eq7 (s : State) (continuation : UInt256) (rho : List UInt256) :
    FirstTable.result7 s (frame continuation) rho = state7 s continuation rho := by
  simp only [FirstTable.result7, eq6]
  rfl
theorem actual_bytes (s : State) (continuation : UInt256) (rho : List UInt256)
    (h : Matches s.memory initial (value s.memory)) (a : Nat) :
    (FirstTable.result7 s (frame continuation) rho).memory[a]?.getD 0 = value s.memory (symbols33 a) := by
  rw [eq7]
  exact matches33 s h a

open GeneralMessageLayout
theorem low_sources : ∀ slot : Fin 61, ∀ j : Fin 4,
    symbols33 (addresses[slot.val]!+28+j.val) = initial (wordAddress StaggerTableLayout.slots[slot.val]!+j.val) := by
  decide +kernel
theorem high_sources : ∀ i : Fin 77, ∀ j : Fin 4,
    symbols33 (addresses[StaggerTableLayout.pairIndices[i.val]!]!+10+j.val) =
      initial (wordAddress Crypto.Ripemd160.rP[i.val+3]!+j.val) := by
  decide +kernel
theorem barrier_sources : ∀ i : Fin 77,
    14 ≤ barriers[i.val]! ∧ barriers[i.val]! ≤ 26 ∧
    symbols33 (addresses[StaggerTableLayout.pairIndices[i.val]!]!+barriers[i.val]!) = 0 := by
  decide +kernel
#print axioms actual_bytes
#print axioms low_sources
#print axioms high_sources
#print axioms barrier_sources
end RipemdMemoryBridge20261028.FirstMemory

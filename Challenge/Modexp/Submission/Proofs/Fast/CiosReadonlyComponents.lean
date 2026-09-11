import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cacheStack (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  baseStack bi pbi pa pb flag target2 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)

def entryPrelude : List Instr :=
  [.push 1 64, .op .MLOAD, .push 1 96, .op .MLOAD, .push 2 9440, .op .MLOAD,
   .push 2 9408, .op .MLOAD, .op .MLOAD, .push 2 9376, .op .MLOAD,
   .push 1 32, .op .MLOAD, .push 2 9408, .op .MLOAD,
   .op (.Dup ⟨7, by decide⟩), .op .ADD,
   .op (.Swap ⟨7, by decide⟩), .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨6, by decide⟩)]

theorem run_entryPrelude (s : State) (pa pb dst ret : UInt256) (n : Nat)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions entryPrelude
      (framed s (UInt256.ofNat 4164) ([pa,pb,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4195)
      ([pa,pb,MachineState.readWord s.memory 9376,MachineState.readWord s.memory (32*n-32),
        MachineState.readWord s.memory 9440,MachineState.readWord s.memory 96,
        MachineState.readWord s.memory 64,MachineState.readWord s.memory 32,
        pa + UInt256.ofNat (32*n-32),dst,ret] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hp96 : (96 : UInt256).toNat = 96 := by decide
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have hp64 : (64 : UInt256).toNat = 64 := by decide
  have hp32 : (32 : UInt256).toNat = 32 := by decide
  have hmod : (32*n-32) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      32*n-32 := Nat.mod_eq_of_lt (by omega)
  have hA := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hB := activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hC := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hD := activeWords_fix s (32*n-32) 32 (by decide) (by omega) hact
  have hE := activeWords_fix s 64 32 (by decide) (by omega) hact
  have hF := activeWords_fix s 32 32 (by decide) (by omega) hact
  have hH := activeWords_fix s 96 32 (by decide) (by omega) hact
  simp [entryPrelude, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hp96, hp9440, hp9376, hp9408, hp64, hp32, hml,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat,
    hmod, hA, hB, hC, hD, hE, hF, hH, List.exchange]

def dropCache : List Instr := [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

theorem run_dropCache (s : State) (tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions dropCache
      (framed s (UInt256.ofNat 4656) ([inv,m0,tl,m96,m64,m32,aEnd,dst,ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4663) ([dst,ret] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [dropCache, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, hc3, hc4, hc5, hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod]

def cachedLoadLow : List Instr := [.op (.Dup ⟨10, by decide⟩), .op .MLOAD]
def cachedMakeMu : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .MUL,
   .op (.Swap ⟨0, by decide⟩)]
def cachedLoadMask : List Instr := [.op (.Dup ⟨8, by decide⟩)]

theorem run_cachedLoadLow (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions cachedLoadLow
      (framed s (UInt256.ofNat 4349)
        (cacheStack bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4351)
      ([MachineState.readWord s.memory (8224+32*n)] ++
        cacheStack bi pbi pa pb flag target2 (UInt256.ofNat (8224+32*n)) inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hmod : (8224+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      8224+32*n := Nat.mod_eq_of_lt (by omega)
  have hactQ := activeWords_fix s (8224+32*n) 32 (by decide) (by omega) hact
  simp [cachedLoadLow, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc17, hc18, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod, hactQ]

theorem run_cachedMakeMu (s : State) (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedMakeMu
      (framed s (UInt256.ofNat 4351)
        ([t0] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4355)
      ([t0, inv*t0] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hc20 : rest.length + 20 < 1024 := by omega
  simp [cachedMakeMu, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc18, hc19, hc20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedLoadMask (s : State) (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions cachedLoadMask
      (framed s (UInt256.ofNat 4355)
        ([t0,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4356)
      ([maxWord,t0,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc19 : rest.length + 19 < 1024 := by omega
  simp [cachedLoadMask, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc19, allOnes_value, Challenge.EvmProof.Word.succ_ofNat_mod]

def makeModProduct : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD]

def finishCarry : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .GT, .op .ADD]

theorem run_cachedMakeModProduct (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions makeModProduct
      (framed s (UInt256.ofNat 4356)
        ([maxWord,t0,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4359)
      ([UInt256.mulMod m0 mu maxWord,t0,mu] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  have hc22 : rest.length + 22 < 1024 := by omega
  simp [makeModProduct,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc20, hc21, hc22,
    allOnes_value, maxWord, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_cachedFinishCarry (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret mm mu t0 : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions finishCarry
      (framed s (UInt256.ofNat 4359)
        ([mm,t0,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4365)
      ([endCarry t0 mm,mu] ++ cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  have hc20 : rest.length + 20 < 1024 := by omega
  have hc21 : rest.length + 21 < 1024 := by omega
  simp [finishCarry,
    runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheStack, baseStack, Nat.add_assoc, hc20, hc21, endCarry,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

def cachedProduct : List Instr :=
  (((cachedLoadLow ++ cachedMakeMu) ++ cachedLoadMask) ++
    makeModProduct) ++ finishCarry

theorem run_cachedProduct (s : State) (bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat) :
    let tl := UInt256.ofNat (8224+32*n)
    let t0 := MachineState.readWord s.memory (8224+32*n)
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4349)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4365)
      ([endCarry t0 (UInt256.mulMod m0 (inv*t0) maxWord),inv*t0] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  let tl := UInt256.ofNat (8224+32*n)
  let t0 := MachineState.readWord s.memory (8224+32*n)
  have h1 := run_cachedLoadLow s bi pbi pa pb flag target2 inv m0 aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have h2 := run_cachedMakeMu s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret t0 rest hcap
  have h3 := run_cachedLoadMask s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h4 := run_cachedMakeModProduct s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret (inv*t0) t0 rest hcap
  have h5 := run_cachedFinishCarry s bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret
    (UInt256.mulMod m0 (inv*t0) maxWord) (inv*t0) t0 rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  exact runInstructions_append_some _ _ _ _ _ h1234 h5

/-- Physical read-only words retained across all CIOS rows. -/
structure ReadonlyCache (mem : ByteArray) (n : Nat) (tl inv m0 : UInt256) : Prop where
  lowAddress : tl = UInt256.ofNat (8224 + 32*n)
  inverse : inv = MachineState.readWord mem 9376
  modulusLow : m0 = MachineState.readWord mem (32*n-32)

theorem ReadonlyCache.of_preserved {mem mem' : ByteArray} {n : Nat}
    {tl inv m0 : UInt256} (h : ReadonlyCache mem n tl inv m0)
    (hinv : MachineState.readWord mem' 9376 = MachineState.readWord mem 9376)
    (hm0 : MachineState.readWord mem' (32*n-32) = MachineState.readWord mem (32*n-32)) :
    ReadonlyCache mem' n tl inv m0 :=
  ⟨h.lowAddress, h.inverse.trans hinv.symm, h.modulusLow.trans hm0.symm⟩

theorem ReadonlyCache.l1 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (bi : UInt256) (pa j : Nat) :
    ReadonlyCache (l1Step mem bi pa n j).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l1Step mem bi pa n 9376 j hn (Or.inr (by decide)))
    (readWord_l1Step mem bi pa n (32*n-32) j hn (Or.inl (by omega)))

theorem ReadonlyCache.l2 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (mu c0 : UInt256) (k : Nat) :
    ReadonlyCache (l2Step mem mu c0 n k).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l2Step mem mu c0 n 9376 k hn (Or.inr (by decide)))
    (readWord_l2Step mem mu c0 n (32*n-32) k hn (Or.inl (by omega)))

theorem ReadonlyCache.middle {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (c : UInt256) :
    ReadonlyCache (midMem mem c) n tl inv m0 :=
  h.of_preserved
    (CiosCachedMidMemory.read_mid mem c 9376 (Or.inr (by decide)))
    (CiosCachedMidMemory.read_mid mem c (32*n-32) (Or.inl (by omega)))

theorem ReadonlyCache.rows {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (pa pb i : Nat) :
    ReadonlyCache (rowsMem mem pa pb n i) n tl inv m0 :=
  h.of_preserved
    (readWord_rowsMem mem pa pb n 9376 hn (Or.inr (by decide)) i)
    (readWord_rowsMem mem pa pb n (32*n-32) hn (Or.inl (by omega)) i)

theorem ReadonlyCache.zeroed {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 32) (s : State) :
    ReadonlyCache (mpZeroed s mem n) n tl inv m0 :=
  h.of_preserved
    (readWord_mpZeroed s mem n 9376 hn (Or.inr (by decide)))
    (readWord_mpZeroed s mem n (32*n-32) hn (Or.inl (by omega)))

theorem run_cachedProduct_model (s : State)
    (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 998) (hn : n ≤ 32)
    (hact : 296 ≤ s.activeWords.toNat)
    (hc : ReadonlyCache s.memory n tl inv m0)
    (hminv : CiosCachedMidMemory.inverseInvariant s.memory n) :
    runInstructions cachedProduct
      (framed s (UInt256.ofNat 4349)
        (cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) =
    some (framed s (UInt256.ofNat 4365)
      ([rowC0 s.memory n,rowMu s.memory n] ++
        cacheStack bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret rest)) := by
  rw [hc.lowAddress, hc.inverse, hc.modulusLow]
  have hr := run_cachedProduct s bi pbi pa pb flag target2
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (32*n-32))
    aEnd m96 m64 m32 dst ret n rest hcap hn hact
  have hcarry := row_carry_swapped (MachineState.readWord s.memory (32*n-32))
    (MachineState.readWord s.memory 9376) (MachineState.readWord s.memory (8224+32*n)) hminv
  simpa only [hcarry, rowC0, rowMu] using hr



end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

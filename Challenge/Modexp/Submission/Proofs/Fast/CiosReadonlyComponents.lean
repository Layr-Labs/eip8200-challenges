import Challenge.Modexp.Submission.Proofs.Fast.N0Carry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry


/-- Physical read-only words retained across all CIOS rows. -/
structure ReadonlyCache (mem : ByteArray) (n : Nat) (tl inv m0 : UInt256) : Prop where
  /-- TL: the frame's `tl` slot holds `mem[0xe0]` (the low modulus word for eight limbs). -/
  lowAddress : tl = MachineState.readWord mem 224
  inverse : inv = MachineState.readWord mem 2720
  modulusLow : m0 = MachineState.readWord mem (16*n+32)
  inverseGuard : inv ≠ UInt256.ofNat 1

theorem ReadonlyCache.of_preserved {mem mem' : ByteArray} {n : Nat}
    {tl inv m0 : UInt256} (h : ReadonlyCache mem n tl inv m0)
    (hinv : MachineState.readWord mem' 2720 = MachineState.readWord mem 2720)
    (hm0 : MachineState.readWord mem' (16*n+32) = MachineState.readWord mem (16*n+32))
    (hn0 : MachineState.readWord mem' 224 = MachineState.readWord mem 224) :
    ReadonlyCache mem' n tl inv m0 :=
  ⟨h.lowAddress.trans hn0.symm, h.inverse.trans hinv.symm, h.modulusLow.trans hm0.symm,
    h.inverseGuard⟩

theorem ReadonlyCache.l1 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (bi : UInt256) (pa j : Nat) :
    ReadonlyCache (l1Step mem bi pa n j).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l1Step mem bi pa n 2720 j hn (Or.inr (by decide)))
    (readWord_l1Step mem bi pa n (16*n+32) j hn (Or.inl (by omega)))
      (readWord_l1Step mem bi pa n 224 j hn (Or.inl (by omega)))

theorem ReadonlyCache.l2 {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (mu c0 : UInt256) (k : Nat) :
    ReadonlyCache (l2Step mem mu c0 n k).memory n tl inv m0 :=
  h.of_preserved
    (readWord_l2Step mem mu c0 n 2720 k hn (Or.inr (by decide)))
    (readWord_l2Step mem mu c0 n (16*n+32) k hn (Or.inl (by omega)))
      (readWord_l2Step mem mu c0 n 224 k hn (Or.inl (by omega)))

theorem ReadonlyCache.middle {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (c : UInt256) :
    ReadonlyCache (midMem mem c) n tl inv m0 :=
  h.of_preserved
    (CiosCachedMidMemory.read_mid mem c 2720 (Or.inr (by decide)))
    (CiosCachedMidMemory.read_mid mem c (16*n+32) (Or.inl (by omega)))
      (CiosCachedMidMemory.read_mid mem c 224 (Or.inl (by omega)))

theorem ReadonlyCache.rows {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (pa pb i : Nat) :
    ReadonlyCache (rowsMem mem pa pb n i) n tl inv m0 :=
  h.of_preserved
    (readWord_rowsMem mem pa pb n 2720 hn (Or.inr (by decide)) i)
    (readWord_rowsMem mem pa pb n (16*n+32) hn (Or.inl (by omega)) i)
      (readWord_rowsMem mem pa pb n 224 hn (Or.inl (by omega)) i)

theorem ReadonlyCache.zeroed {mem : ByteArray} {n : Nat} {tl inv m0 : UInt256}
    (h : ReadonlyCache mem n tl inv m0) (hn : n ≤ 8) (s : State) :
    ReadonlyCache (mpZeroed s mem n) n tl inv m0 :=
  h.of_preserved
    (readWord_mpZeroed s mem n 2720 hn (Or.inr (by decide)))
    (readWord_mpZeroed s mem n (16*n+32) hn (Or.inl (by omega)))
      (readWord_mpZeroed s mem n 224 hn (Or.inl (by omega)))

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

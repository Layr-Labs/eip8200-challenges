import Challenge.Modexp.Submission.Proofs.Fast.TnCacheExtraTrace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheLastTrace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Chain

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore

/-- The shared three-cell suffix includes its real entry JUMPDEST. -/
def suffix : List Instr :=
  (([.op .JUMPDEST] ++ TnCacheExtraTrace.extraProgram 1 2176 2208) ++
    TnCacheExtraTrace.extraProgram 2 2144 2176) ++
    CiosCachedLast.l2LastProgram 0 0 2112 2144

/-- The first four cells of the eight-limb reduction reach the shared suffix. -/
def prefixProgram : List Instr :=
  ((([.op .JUMPDEST] ++ l2Program 10 192 2304 2336) ++
    l2Program 1 160 2272 2304) ++ l2Program 1 128 2240 2272) ++
    TnCacheExtraTrace.extraProgram 0 2208 2240

theorem run_suffix (s : State) (pc : Nat) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : k+4 = n)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    runInstructions suffix
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n k
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+100)) mem bi mu c0 n (k+3)
      pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have h0 : runInstructions [.op .JUMPDEST]
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n k
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (TnCacheL2Trace.state s (UInt256.ofNat (pc+1)) mem bi mu c0 n k
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
    simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL2Trace.state,
      Challenge.EvmProof.Word.succ_ofNat_mod]
    omega
  have h1 := TnCacheExtraTrace.run_extraStep 1 s (UInt256.ofNat (pc+1)) mem bi mu c0 n k
    64 2176 2208 (by change 64 = _; omega) (by decide)
    (by change 2176 = _; omega) (by change 2208 = _; omega)
    pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hn (by omega) hc
  have h2 := TnCacheExtraTrace.run_extraStep 2 s (UInt256.ofNat (pc+34)) mem bi mu c0 n (k+1)
    32 2144 2176 (by change 32 = _; omega) (by decide)
    (by change 2144 = _; omega) (by change 2176 = _; omega)
    pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact hn (by omega) hc
  have h3 := TnCacheLastTrace.run_stepLast 0 s (UInt256.ofNat (pc+67)) mem bi mu c0 n (k+2)
    0 2112 2144 (by change 0 = _; omega) (by change 2112 = _; omega) (by change 2144 = _; omega)
    pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn (by omega) (by intro _; rfl)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

theorem run_prefix (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    runInstructions prefixProgram
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheL2Trace.state s (UInt256.ofNat (pc+148)) mem bi mu c0 8 4
      pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h0 : runInstructions [.op .JUMPDEST]
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (TnCacheL2Trace.state s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
    simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL2Trace.state,
      Challenge.EvmProof.Word.succ_ofNat_mod]
    omega
  have h1 := TnCacheL2Trace.run_step 10 s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
    192 2304 2336 (by decide) (by decide) (by decide)
    pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h2 := TnCacheL2Trace.run_step 1 s (UInt256.ofNat (pc+45)) mem bi mu c0 8 1
    160 2272 2304 (by decide) (by decide) (by decide)
    pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h3 := TnCacheL2Trace.run_step 1 s (UInt256.ofNat (pc+80)) mem bi mu c0 8 2
    128 2240 2272 (by decide) (by decide) (by decide)
    pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h4 := TnCacheExtraTrace.run_extraStep 0 s (UInt256.ofNat (pc+115)) mem bi mu c0 8 3
    96 2208 2240 (by decide) (by decide) (by decide) (by decide)
    pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact (by decide) (by decide) hc
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd, Fin.val_ofNat] at h1 h2 h3 h4
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  exact runInstructions_append_some _ _ _ _ _ h0123 h4

#print axioms run_suffix
#print axioms run_prefix

def fullProgram (n : Nat) : List Instr :=
  if n = 4 then suffix else prefixProgram ++ suffix

def fullSize (n : Nat) : Nat := if n = 4 then 100 else 248

/-- All reduction cells preserve the arbitrary cached carry slot and consume mu. -/
theorem run_full (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    runInstructions (fullProgram n)
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n 0
        pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+fullSize n)) mem bi mu c0 n (n-1)
      pbi hd pb ent tn target inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  rcases hn with rfl | rfl
  · simpa [fullProgram, fullSize] using
      run_suffix s pc mem bi mu c0 4 0 pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret
        rest hcap hact (by decide) (by decide) hc
  · have hp := run_prefix s pc mem bi mu c0 pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact hc
    have hs := run_suffix s (pc+148) mem bi mu c0 8 4 pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact (by decide) (by decide) hc
    have both := runInstructions_append_some _ _ _ _ _ hp hs
    simpa [fullProgram, fullSize, Nat.add_assoc] using both

#print axioms run_full
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Chain

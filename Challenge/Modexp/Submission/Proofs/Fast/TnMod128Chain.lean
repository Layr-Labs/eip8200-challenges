import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Chain
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Trace

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
/-- The shared three-cell suffix with its entry JUMPDEST (P1): the fifth cell reads modulus[64]
from the eleventh frame word and the sixth reads modulus[32] from the eighth; the Montgomery
inverse rides in the fifteenth word and the carry cache in the sixteenth. -/
def suffix : List Instr :=
  (([.op .JUMPDEST] ++ TnMod128Trace.program64) ++
    TnMod128Trace.program32) ++
    CiosCachedLast.l2LastProgram 0 0 2112 2144

theorem run_suffix (s : State) (pc : Nat) (mem : ByteArray)
    (bi mu c0 : UInt256) (n k : Nat)
    (pbi hd pb ent tn target tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat) (hn : n ≤ 8) (hk : k+4 = n)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32) :
    runInstructions suffix
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n k
        pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+100)) mem bi mu c0 n (k+3)
      pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h0 : runInstructions [.op .JUMPDEST]
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n k
        pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
      some (TnCacheL2Trace.state s (UInt256.ofNat (pc+1)) mem bi mu c0 n k
        pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
    simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL2Trace.state,
      Challenge.EvmProof.Word.succ_ofNat_mod]
    omega
  have h1 := TnMod128Trace.run_step64 s (UInt256.ofNat (pc+1)) mem bi mu c0 n k
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact hn hk hc.word64
  have h2 := TnMod128Trace.run_step32 s (UInt256.ofNat (pc+34)) mem bi mu c0 n (k+1)
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact hn (by omega) hc.word32
  have h3 := TnCacheLastTrace.run_stepLast 0 s (UInt256.ofNat (pc+67)) mem bi mu c0 n (k+2)
    0 2112 2144 (by change 0 = _; omega) (by change 2112 = _; omega) (by change 2144 = _; omega)
    pbi hd pb ent m32 target m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hn (by omega) (by intro _; rfl)
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd] at h1 h2 h3
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  exact runInstructions_append_some _ _ _ _ _ h012 h3

/-- Four cells; the second reads modulus[160] from the `m0` frame slot and the third
reads modulus[128] from the cached frame slot. -/
def prefixProgram : List Instr :=
  ((([.op .JUMPDEST] ++ l2Program 2 192 2304 2336) ++
    TnMod128Trace.program160) ++ TnMod128Trace.program) ++
    TnCacheExtraTrace.extraProgramZeroNarrow 2208 2240

theorem run_prefix (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128)
    (hm0 : m0 = MachineState.readWord mem 160) :
    runInstructions prefixProgram
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheL2Trace.state s (UInt256.ofNat (pc+134)) mem bi mu c0 8 4
      pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h0 : runInstructions [.op .JUMPDEST]
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
      some (TnCacheL2Trace.state s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
    simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL2Trace.state,
      Challenge.EvmProof.Word.succ_ofNat_mod]
    omega
  have h1 := TnCacheL2Trace.run_step 2 s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
    192 2304 2336 (by decide) (by decide) (by decide)
    pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h2 := TnMod128Trace.run_step160 s (UInt256.ofNat (pc+37)) mem bi mu c0
    pbi hd pb ent m32 m128 m64 m0 (tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    (by simp only [List.length_cons]; omega) hact hm0
  have h3 := TnMod128Trace.run_step s (UInt256.ofNat (pc+69)) mem bi mu c0
    pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)
    hrest hact hcache
  have h4 := TnCacheExtraTrace.run_extraStepZeroNarrow s (UInt256.ofNat (pc+102)) mem bi mu c0 8 3
    96 2208 2240 (by decide) (by decide) (by decide) (by decide)
    pbi hd pb ent m32 m128 tl m64 m0 aEnd m96 inv tn dst ret rest hcap hact (by decide) (by decide) hc
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd, Fin.val_ofNat] at h1 h2 h3 h4
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  exact runInstructions_append_some _ _ _ _ _ h0123 h4


def fullProgram (n : Nat) : List Instr :=
  if n = 4 then suffix else prefixProgram ++ suffix

def fullSize (n : Nat) : Nat := if n = 4 then 100 else 234

/-- All reduction cells preserve the arbitrary cached carry slot and consume mu. -/
theorem run_full (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128)
    (hm0 : n = 8 → m0 = MachineState.readWord mem 160) :
    runInstructions (fullProgram n)
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n 0
        pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+fullSize n)) mem bi mu c0 n (n-1)
      pbi hd pb ent m32 m128 m64 (m0 :: tl :: m96 :: inv :: tn :: aEnd :: dst :: ret :: rest)) := by
  rcases hn with rfl | rfl
  · simpa [fullProgram, fullSize] using
      run_suffix s pc mem bi mu c0 4 0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
        rest hcap hact (by decide) (by decide) hc
  · have hp := run_prefix s pc mem bi mu c0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact hc hcache (hm0 rfl)
    have hs := run_suffix s (pc+134) mem bi mu c0 8 4 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact (by decide) (by decide) hc
    have both := runInstructions_append_some _ _ _ _ _ hp hs
    simpa [fullProgram, fullSize, Nat.add_assoc] using both


#print axioms run_suffix
#print axioms run_prefix
#print axioms run_full
end Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain

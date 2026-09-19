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
abbrev suffix : List Instr :=
  Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Chain.suffix

/-- Four cells; the third reads modulus[128] from the cached frame slot. -/
def prefixProgram : List Instr :=
  ((([.op .JUMPDEST] ++ l2Program 1 192 2304 2336) ++
    l2Program 1 160 2272 2304) ++ TnMod128Trace.program) ++
    TnCacheExtraTrace.extraProgramZeroNarrow 2208 2240

theorem run_prefix (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128) :
    runInstructions prefixProgram
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheL2Trace.state s (UInt256.ofNat (pc+136)) mem bi mu c0 8 4
      pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  have hrest : (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest).length ≤ 1006 := by
    simp only [List.length_cons]; omega
  have h0 : runInstructions [.op .JUMPDEST]
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 8 0
        pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
      some (TnCacheL2Trace.state s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
        pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
    simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr, TnCacheL2Trace.state,
      Challenge.EvmProof.Word.succ_ofNat_mod]
    omega
  have h1 := TnCacheL2Trace.run_step 1 s (UInt256.ofNat (pc+1)) mem bi mu c0 8 0
    192 2304 2336 (by decide) (by decide) (by decide)
    pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h2 := TnCacheL2Trace.run_step 1 s (UInt256.ofNat (pc+36)) mem bi mu c0 8 1
    160 2272 2304 (by decide) (by decide) (by decide)
    pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact (by decide) (by decide) (by decide)
  have h3 := TnMod128Trace.run_step s (UInt256.ofNat (pc+71)) mem bi mu c0
    pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)
    hrest hact hcache
  have h4 := TnCacheExtraTrace.run_extraStepZeroNarrow s (UInt256.ofNat (pc+104)) mem bi mu c0 8 3
    96 2208 2240 (by decide) (by decide) (by decide) (by decide)
    pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret rest hcap hact (by decide) (by decide) hc
  simp only [Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_assoc, Nat.reduceAdd, Fin.val_ofNat] at h1 h2 h3 h4
  have h01 := runInstructions_append_some _ _ _ _ _ h0 h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  exact runInstructions_append_some _ _ _ _ _ h0123 h4


def fullProgram (n : Nat) : List Instr :=
  if n = 4 then suffix else prefixProgram ++ suffix

def fullSize (n : Nat) : Nat := if n = 4 then 100 else 236

/-- All reduction cells preserve the arbitrary cached carry slot and consume mu. -/
theorem run_full (s : State) (pc : Nat) (mem : ByteArray) (bi mu c0 : UInt256)
    (n : Nat) (hn : n = 4 ∨ n = 8)
    (pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 88 ≤ s.activeWords.toNat)
    (hc : TnCacheExtraTrace.ExtraCache mem m96 m64 m32)
    (hcache : m128 = MachineState.readWord mem 128) :
    runInstructions (fullProgram n)
      (TnCacheL2Trace.state s (UInt256.ofNat pc) mem bi mu c0 n 0
        pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) =
    some (TnCacheLastTrace.lastState s (UInt256.ofNat (pc+fullSize n)) mem bi mu c0 n (n-1)
      pbi hd pb ent tn m128 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)) := by
  rcases hn with rfl | rfl
  · simpa [fullProgram, fullSize] using
      TnCacheL2Chain.run_suffix s pc mem bi mu c0 4 0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
        rest hcap hact (by decide) (by decide) hc
  · have hp := run_prefix s pc mem bi mu c0 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact hc hcache
    have hs := TnCacheL2Chain.run_suffix s (pc+136) mem bi mu c0 8 4 pbi hd pb ent tn m128 tl inv m0 aEnd m96 m64 m32 dst ret
      rest hcap hact (by decide) (by decide) hc
    have both := runInstructions_append_some _ _ _ _ _ hp hs
    simpa [fullProgram, fullSize, Nat.add_assoc] using both


#print axioms run_prefix
#print axioms run_full
end Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain

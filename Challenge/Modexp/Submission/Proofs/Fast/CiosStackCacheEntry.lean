import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheReadOnly
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 300000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Entry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

/-- Entry of the selected cached CIOS bytecode; virtual entry proofs remain separate. -/
def artifactEntryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4160
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, dst, ret] ++ rest
           memory := mem }

theorem word_zero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide

def zeroCache (mem : ByteArray) : CachedMemory :=
  ⟨mem, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩

def loadA : List Instr := CiosStackCachePrograms.prologue.take 5
def loadB : List Instr := (CiosStackCachePrograms.prologue.drop 5).take 4
def loadC : List Instr := (CiosStackCachePrograms.prologue.drop 9).take 3
def reorder : List Instr := CiosStackCachePrograms.prologue.drop 12

theorem prologue_split : CiosStackCachePrograms.prologue = ((loadA ++ loadB) ++ loadC) ++ reorder := rfl

set_option linter.unusedSimpArgs false in
theorem run_loadA (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions loadA (framed s (UInt256.ofNat 4160) rest) =
    some (framed s (UInt256.ofNat 4169) ([MachineState.readWord s.memory 9376, MachineState.readWord s.memory 9440] ++ rest)) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hp9376 : (9376 : UInt256).toNat = 9376 := by decide
  have ha9376 := activeWords_fix s 9376 32 (by decide) (by omega) hact
  have hp9440 : (9440 : UInt256).toNat = 9440 := by decide
  have ha9440 := activeWords_fix s 9440 32 (by decide) (by omega) hact
  simp [loadA, CiosStackCachePrograms.prologue, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, word_zero, h0, h1, h2,
    hp9376, ha9376, hp9440, ha9440, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_loadB (s : State) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions loadB (framed s (UInt256.ofNat 4169) rest) =
    some (framed s (UInt256.ofNat 4174) ([MachineState.readWord s.memory 0, MachineState.readWord s.memory 32] ++ rest)) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hp0 : (0 : UInt256).toNat = 0 := by decide
  have ha0 := activeWords_fix s 0 32 (by decide) (by omega) hact
  have hp32 : (32 : UInt256).toNat = 32 := by decide
  have ha32 := activeWords_fix s 32 32 (by decide) (by omega) hact
  simp [loadB, CiosStackCachePrograms.prologue, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, word_zero, h0, h1, h2,
    hp0, ha0, hp32, ha32, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_loadC (s : State) (n : Nat) (rest : List UInt256) (hcap : rest.length ≤ 1010)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32) (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions loadC (framed s (UInt256.ofNat 4174) rest) =
    some (framed s (UInt256.ofNat 4179) ([MachineState.readWord s.memory (32*n-32)] ++ rest)) := by
  have h0 : rest.length < 1024 := by omega
  have h1 : rest.length+1 < 1024 := by omega
  have h2 : rest.length+2 < 1024 := by omega
  have hp9408 : (9408 : UInt256).toNat = 9408 := by decide
  have ha9408 := activeWords_fix s 9408 32 (by decide) (by omega) hact
  have hm : (32*n-32) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n-32 := Nat.mod_eq_of_lt (by omega)
  have ham := activeWords_fix s (32*n-32) 32 (by decide) (by omega) hact
  simp [loadC, CiosStackCachePrograms.prologue, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, word_zero, h0, h1, h2,
    hp9408, ha9408, hm, ham, hml, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_reorder (s : State) (r : ReadOnlyCache) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) :
    runInstructions reorder
      (framed s (UInt256.ofNat 4179) ([r.m0, r.z0, r.m32, r.inv, r.tl, pa, pb, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4192) ([pa, pb] ++ cacheTail (zeroCache s.memory) r dst ret rest)) := by
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  simp [reorder, CiosStackCachePrograms.prologue, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheTail, zeroCache, word_zero, h9, h10, h11, h12, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_prologue (s : State) (n : Nat) (pa pb dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn32 : n ≤ 32)
    (hml : MachineState.readWord s.memory 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions CiosStackCachePrograms.prologue
      (framed s (UInt256.ofNat 4160) ([pa, pb, dst, ret] ++ rest)) =
    some (framed s (UInt256.ofNat 4192)
      ([pa, pb] ++ cacheTail (zeroCache s.memory) (ReadOnlyCache.capture s.memory n) dst ret rest)) := by
  let r := ReadOnlyCache.capture s.memory n
  have h1 := run_loadA s ([pa, pb, dst, ret] ++ rest) (by simp; omega) hact
  have h2 := run_loadB s ([r.inv, r.tl, pa, pb, dst, ret] ++ rest) (by simp; omega) hact
  have h3 := run_loadC s n ([r.z0, r.m32, r.inv, r.tl, pa, pb, dst, ret] ++ rest)
    (by simp; omega) hact hn32 hml
  have h4 := run_reorder s r pa pb dst ret rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  simpa only [prologue_split, r, ReadOnlyCache.capture, List.append_assoc,
    List.cons_append, List.nil_append] using h1234

set_option linter.unusedSimpArgs false in
theorem run_head (s : State) (c : CachedMemory) (r : ReadOnlyCache) (n : Nat)
    (pa pb dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord s.memory 9344 = UInt256.ofNat (32*n)) :
    runInstructions CiosStackCachePrograms.entryHead
      (framed s (UInt256.ofNat 4192) ([pa, pb] ++ cacheTail c r dst ret rest)) =
    some (framed s (UInt256.ofNat 4208)
      ([pa, pb, isFour n, negative32, allOnes] ++ cacheTail c r dst ret rest)) := by
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have hp : (9344 : UInt256).toNat = 9344 := by decide
  have h128 : (128 : UInt256) = UInt256.ofNat 128 := by decide
  have ha := activeWords_fix s 9344 32 (by decide) (by omega) hact
  simp [CiosStackCachePrograms.entryHead, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheTail, isFour, negative32, allOnes,
    CompactConstants.notZeroStruct, CompactConstants.notZero, CompactConstants.notThirtyOne, h12, h13, h14, h15, h16, h17,
    hp, h128, ha, hs32, List.exchange, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  decide

theorem entryBody_eq : CiosStackCachePrograms.entryBody = CiosCached.entryBodyProgram := rfl

/-- The new prologue adds the eight cache words. The accepted entry body still
performs the same zero-fill and pointer calculations. -/
theorem run_entry (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) (hn : 3 ≤ n) (hn32 : n ≤ 32)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = UInt256.ofNat (32*n-32)) :
    runInstructions CiosStackCachePrograms.entry
      (artifactEntryState s mem pa pb dst ret rest) =
    some (framed { s with memory := mpZeroed s mem n } (UInt256.ofNat 4243)
      (rowFrame (initial s mem n) (ReadOnlyCache.capture mem n)
        (UInt256.ofNat (ptrAt (pb+32*n-32) 0)) (UInt256.ofNat (pa+32*n-32))
        (UInt256.ofNat (pb-32)) (isFour n) dst ret rest)) := by
  let r := ReadOnlyCache.capture mem n
  let suffix := [UInt256.ofNat 0, r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest
  have hsuffix : suffix.length ≤ 1006 := by
    simp only [suffix, List.length_append, List.length_cons, List.length_nil]
    omega
  have hp := run_prologue { s with memory := mem } n (UInt256.ofNat pa) (UInt256.ofNat pb)
    dst ret rest hcap hact hn32 hml
  have hh := run_head { s with memory := mem } (zeroCache mem) r n (UInt256.ofNat pa)
    (UInt256.ofNat pb) dst ret rest hcap hact hs32
  have hb := CiosStackCacheInitBody.run_entryBody s mem pa pb n (UInt256.ofNat 0) (UInt256.ofNat 0)
    suffix hsuffix hrun hact (by omega) hn32 hpa hpaFit hpb hpbFit hcds hs32
  rw [← entryBody_eq] at hb
  have hph := runInstructions_append_some _ _ _ _ _ hp hh
  have hphb := runInstructions_append_some _ _ _ _ _ hph hb
  simpa only [CiosStackCachePrograms.entry_split, artifactEntryState,
    CiosStackCacheInitBody.cachedEntryState, CiosStackCacheInitBody.outState, framed, zeroCache, initial,
    rowFrame, cacheTail, r, suffix, List.append_assoc, List.cons_append, List.nil_append] using hphb

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Entry

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Entry.run_entry

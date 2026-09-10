import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Exit

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

def dropFrame : List Instr := CiosStackCachePrograms.exit.take 6
def flush : List Instr := (CiosStackCachePrograms.exit.drop 6).take 6
def returnBlock : List Instr := CiosStackCachePrograms.exit.drop 12

theorem split_program : CiosStackCachePrograms.exit = (dropFrame ++ flush) ++ returnBlock := rfl

def suffix (r : ReadOnlyCache) (dst ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [r.m0, r.z0, r.m32, r.inv, r.tl, dst, ret] ++ rest

set_option linter.unusedSimpArgs false in
theorem run_dropFrame (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    runInstructions dropFrame
      (framed s (UInt256.ofNat 4855) (rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4861) (cacheTail c r dst ret rest)) := by
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have h12 : rest.length+12 < 1024 := by omega
  have h13 : rest.length+13 < 1024 := by omega
  have h14 : rest.length+14 < 1024 := by omega
  have h15 : rest.length+15 < 1024 := by omega
  have h16 : rest.length+16 < 1024 := by omega
  simp [dropFrame, CiosStackCachePrograms.exit, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail,
    h10, h11, h12, h13, h14, h15, h16, Challenge.EvmProof.Word.succ_ofNat_mod]

set_option linter.unusedSimpArgs false in
theorem run_flush (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions flush
      (framed { s with memory := c.memory } (UInt256.ofNat 4861) (cacheTail c r dst ret rest)) =
    some (framed { s with memory := c.virtual } (UInt256.ofNat 4873) (suffix r dst ret rest)) := by
  have h8 : rest.length+8 < 1024 := by omega
  have h9 : rest.length+9 < 1024 := by omega
  have h10 : rest.length+10 < 1024 := by omega
  have h11 : rest.length+11 < 1024 := by omega
  have hp0 : (8256 : UInt256).toNat = 8256 := by decide
  have hp1 : (8288 : UInt256).toNat = 8288 := by decide
  have hp2 : (8320 : UInt256).toNat = 8320 := by decide
  have ha0 := activeWords_fix s 8256 32 (by decide) (by omega) hact
  have ha1 := activeWords_fix s 8288 32 (by decide) (by omega) hact
  have ha2 := activeWords_fix s 8320 32 (by decide) (by omega) hact
  simp [flush, CiosStackCachePrograms.exit, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, cacheTail, suffix, CachedMemory.virtual, storeWord,
    h8, h9, h10, h11, hp0, hp1, hp2, ha0, ha1, ha2, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_returnBlock (s : State) (r : ReadOnlyCache) (dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 2220 = true) :
    runInstructions returnBlock
      (framed s (UInt256.ofNat 4873) (suffix r dst ret rest)) =
    some (framed s (UInt256.ofNat 2220) ([dst, ret] ++ rest)) := by
  have h2 : rest.length+2 < 1024 := by omega
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have h6 : rest.length+6 < 1024 := by omega
  have h7 : rest.length+7 < 1024 := by omega
  simp [returnBlock, CiosStackCachePrograms.exit, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, suffix,
    h2, h3, h4, h5, h6, h7, htarget, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]

/-- All cache words are flushed before the existing CSUB routine is entered. -/
theorem run_exit (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (htarget : Decode.isValidJumpDest s.executionEnv.code 2220 = true) :
    runInstructions CiosStackCachePrograms.exit
      (framed { s with memory := c.memory } (UInt256.ofNat 4855)
        (rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed { s with memory := c.virtual } (UInt256.ofNat 2220) ([dst, ret] ++ rest)) := by
  rw [split_program]
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_dropFrame { s with memory := c.memory } c r pbi paEnd pbEnd flag dst ret rest hcap)
      (run_flush s c r dst ret rest hcap hact))
    (run_returnBlock { s with memory := c.virtual } r dst ret rest hcap htarget)

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Exit

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Exit.run_exit

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailStore

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedTailDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option linter.unusedSimpArgs false in
theorem run_cleanup (s : State) (c mu bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) :
    runInstructions cleanupProgram (input s c mu bi pbi paEnd pbEnd flag dst ret rest) =
    some (cleaned s c pbi paEnd pbEnd flag dst ret rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  simp [cleanupProgram, tailLoopProgram, CiosCached.tailProgram, input, cleaned, baseStack, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hc9, hc10, hc11,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

set_option linter.unusedSimpArgs false in
theorem run_store (s : State) (c pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions storeProgram (cleaned s c pbi paEnd pbEnd flag dst ret rest) =
    some (stored s c pbi paEnd pbEnd flag dst ret rest) := by
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have hc11 : rest.length+12 < 1024 := by omega
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) =
      s.activeWords := activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) =
      s.activeWords := activeWords_fix s 8256 32 (by decide) (by omega) hact
  simp [storeProgram, tailLoopProgram, CiosCached.tailProgram, cleaned, stored, baseStack, framed, tailMem, tailMem1,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11,
    h8192, h8224, h8256, hactP, hactN, hactT, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedTailStore

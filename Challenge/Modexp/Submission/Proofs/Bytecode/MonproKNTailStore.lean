import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailStore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache MonproKNRowPrograms MonproKNTailDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_cleanup (s : State) (pmj ptj c mu bi pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) :
    runInstructions cleanupProgram (input s pmj ptj c mu bi pbi paEnd pbEnd dst ret rest) =
    some (cleaned s c pbi paEnd pbEnd dst ret rest) := by
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  simp [cleanupProgram, tailProgram, input, cleaned, baseStack, framed,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hc9, hc10, hc11, hc12,
    List.exchange, Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_store (s : State) (c pbi paEnd pbEnd dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1007) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions storeProgram (cleaned s c pbi paEnd pbEnd dst ret rest) =
    some (stored s c pbi paEnd pbEnd dst ret rest) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have h8256 : (8256 : UInt256).toNat = 8256 := by decide
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8192 32) =
      s.activeWords := activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8256 32) =
      s.activeWords := activeWords_fix s 8256 32 (by decide) (by omega) hact
  simp [storeProgram, tailProgram, cleaned, stored, baseStack, framed, tailMem, tailMem1,
    runInstructions, Challenge.EvmProof.Stepper.runInstr, hc8, hc9, hc10, hc11,
    h8192, h8224, h8256, hactP, hactN, hactT, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNTailStore

import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidDefs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000


namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidStore

open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCached CiosCachedMidDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_store (s : State) (c bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 1006) (hact : 91 ≤ s.activeWords.toNat) :
    runInstructions storeProgram (input s c bi pbi paEnd pbEnd flag dst ret rest) =
      some (stored s c bi pbi paEnd pbEnd flag dst ret rest) := by
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have hc11 : rest.length+12 < 1024 := by omega
  have hc12 : rest.length+13 < 1024 := by omega
  have h8224 : (2080 : UInt256).toNat = 2080 := by decide
  have h8192 : (2048 : UInt256).toNat = 2048 := by decide
  have hactN : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2080 32) =
      s.activeWords := activeWords_fix s 2080 32 (by decide) (by omega) hact
  have hactP : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 2048 32) =
      s.activeWords := activeWords_fix s 2048 32 (by decide) (by omega) hact
  simp [storeProgram, midProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    input, stored, baseStack, framed, midMem, midMem1,
    hc9, hc10, hc11, hc12, h8224, h8192, hactN, hactP,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidStore
